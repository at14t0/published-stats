#### Necessary libraries
## install.packages(c("tidyr","dplyr","tibble","stringr","lubridate","forcats","ggplot2","ROCit","rstanarm","doMC","survival","survminer"))

library(tidyverse)
library(partykit)
library(haven)
library(lubridate)
library(forcats)
library(ROCit)
library(survival)
library(survminer)
library(rstanarm)
library(projpred)
library(MCMCvis)
library(rcompanion)
library(xlsx)
library(doMC)
library(reshape2)
registerDoMC(cores=6)
options(mc.cores = parallel::detectCores())

noNA <- function(n){return(!anyNA(n))}
is.data.useful <- function(x){
  return(
  (length(na.omit(x))/length(x)>0.7)
  &&
  (sort(table(na.omit(x)),decreasing=TRUE)[1]/length(na.omit(x))<0.9)
  )
}
col_gen <- function(col){
  if(anyNA(col))
    d <- paste0(" [",length(na.omit(col))," of ",length(col),"]")
  else
    d <- ""
  res <- paste0("n= ", length(na.omit(col)))
  if(!any(!(col==0 | col==1),na.rm=TRUE) && !is.factor(col)){
    res <- paste0(sum(na.omit(col))," (",round(sum(na.omit(col))/length(na.omit(col))*100,2),"%)")
  }else if(is.factor(col)){
    fact <- table(na.omit(col))
    res <- paste0(rownames(fact), ": ", fact," (",round(fact/length(na.omit(col))*100,2),"%)", collapse = " | ")
  }else if(is.numeric(col)){
    q <- quantile(na.omit(col),probs=c(0.5,0.25,0.75))
    res <- paste0("Median/IQR: ",round(q[1],2)," (",round(q[2],2),"-",round(q[3],2),") Mean/SD: ",round(mean(na.omit(col)),2)," (+/-",round(sd(na.omit(col)),2),")")
  }
  return(c(res,d))
}
col_test <- function(col,f1,f2){
  if(!(is.factor(col)||is.numeric(col)) || length(unique(col))<2 ||length(na.omit(col[which(f1)]))<3 || length(na.omit(col[which(f2)]))<3){
    return(c("no testing possible",""))
  }

  if(is.factor(col)||length(unique(col))<6){
    t <- chisq.test(cbind(table(na.omit(col[which(f1)])),table(na.omit(col[which(f2)]))))
    test <- "Chi-Squared"
    if(is.nan(t$p.value)){
      res <-"-"}
    else
    {
      if(t$p.value<0.001){
        res <- "p<0.001"
      }
      else{
        res <- paste0("p= ",round(t$p.value,4))
      }
    }

  }
  else{
    if(length(na.omit(col[which(f1)]))>10 && length(na.omit(col[which(f2)]))>10){
      t <- t.test(na.omit( col[which(f1)] ),na.omit( col[which(f2)] ))
      test <- "T-Test"
      if(is.nan(t$p.value)){
        res <-"-"}
      else
      {
        if(t$p.value<0.001){
          res <- "p<0.001"
        }
        else{
          res <- paste0("p= ",round(t$p.value,4))
        }
      }
    }
    else{
      t <- wilcox.test(na.omit( col[which(f1)] ),na.omit( col[which(f2)] ))
      test <- "Rank-Sum"
      if(is.nan(t$p.value)){
        res <-"-"}
      else
      {
        if(t$p.value<0.001){
          res <- "p<0.001"
        }
        else{
          res <- paste0("p= ",round(t$p.value,4))
        }
      }
    }
  }
  return(c(res,test))
}

create_models <- function(data,dependent,vars,interactions, prior=lasso(df=1,autoscale=TRUE)){
  modellist <- list()
  null_formula <- as.formula(paste0(dependent,"~1"))
  full_formula <- paste0(dependent, "~",paste0(vars,collapse="+"))
  if(!is.null(interactions)){
    vars <- vars[which(!(vars %in% interactions))]
    for(i in seq_along(interactions)){
      full_formula <- paste0(full_formula,"+",paste0(vars,":",interactions[i], collapse="+"))
    }
  }
  full_formula <-as.formula(full_formula)
  modellist <- c(modellist,"null_formula"=null_formula, "full_formula"=full_formula)
  print("Null model")
  modellist[["stanreg_models"]] <- stanreg_list(stan_glm(null_formula,data=data,family=binomial(link= "logit"), prior_intercept=normal(0,1), cores =4, seed=1234),model_names= "model0")
  print("Full model")
  modellist[["stanreg_models"]][["model10"]] <-  stan_glm(full_formula,data=data,family=binomial(link= "logit"),prior=prior, prior_intercept=normal(0,1), cores =4, seed=1234)
  for(i in 1:9){
    temp<-MCMCsummary(modellist[["stanreg_models"]][["model10"]],HPD=TRUE,hpd_prob=0.1*i)%>%as.data.frame %>% rownames_to_column %>% filter(rowname!= "mean_PPD" & rowname!= "log-posterior" & rowname!="(Intercept)")
    colnames(temp)<- c("name","mean","sd","lower","upper","rhat","neff")
    temp_vars<-temp %>% filter(sign(lower)==sign(upper))%>%select(name)%>%unlist
    if(length(temp_vars>0)){
      print(paste0("Calculating model ",i))
      temp_vars_pass <- temp_vars[which(temp_vars %in% vars)]
      temp_vars_fail <-temp_vars[which(!( temp_vars %in% vars )&!(temp_vars %in% interactions))]
      for(j in seq_along(temp_vars_fail)){
        if(!str_detect(temp_vars_fail[j],":")){
          temp_vars_pass <- c(temp_vars_pass, paste0("as.numeric(",str_sub(temp_vars_fail[j],end=-2),"==",str_sub(temp_vars_fail[j],start=-1),")"))
        }
        else{
          temp_split <- str_split(temp_vars_fail[j],":") %>% unlist
          if(!(temp_split[1] %in% vars)&!(temp_split[1] %in% interactions)){
            temp_vars_pass <- c(temp_vars_pass, paste0("as.numeric(",str_sub(temp_split[1],end=-2),"==",str_sub(temp_split[1],start=-1),"):",temp_split[2]))

          }else if(!(temp_split[2] %in% vars)&!(temp_split[2] %in% interactions)){
            temp_vars_pass <- c(temp_vars_pass, paste0(temp_split[1],":as.numeric(",str_sub(temp_split[2],end=-2),"==",str_sub(temp_split[2],start=-1),")"))
          }else{
            temp_vars_pass <- c(temp_vars_pass,temp_vars_fail[j])
          }
        }
      }
      temp_formula <- as.formula(paste0(dependent,"~",paste0(temp_vars_pass,collapse="+")))
      modellist[[paste0("hpd",i)]]<- temp
      modellist[["stanreg_models"]][[paste0("model",i)]]<-stan_glm(temp_formula,data=data,family=binomial(link= "logit"),prior=prior, prior_intercept=normal(0,1), cores =4, seed=1234)
    }else{
print(paste0("Hpd ",i," did not have any predictors."))
        }
  }

  return(modellist)
}
compare_models_at <- function(modellist){
  loos <- list()
  print(modellist[["stanreg_models"]])
  for(i in 0:10){
    if(!is.null(modellist[["stanreg_models"]][[paste0("model",i)]])){

      loos[[paste0("loo",i)]] <- loo(modellist[["stanreg_models"]][[paste0("model",i)]])
    }
  }
  return(loo_compare(loos))
}

dlaplace <- function(x, location, scale) {
    0.5 / scale * exp(-abs(x - location) / scale)
  }
stat_dist <- function(dist, ...) {
    ggplot2::stat_function(ggplot2::aes_(color = dist), ...)
  }
  prio<-ggplot() +
    xlim(-5,5)+
    stat_dist("Intercept prior", size = 1, fun = dnorm,
              args = list(mean = 0, sd = 1)) +
     stat_dist("Prior for EPV <5", size =1, fun = dnorm,
              args = list(mean = 0, sd = .5)) +
    stat_dist("Prior for EPV >5", size =1, fun = dlaplace,
              args = list(location = 0, scale = .5)) +
    theme_classic()+
    labs(y=NULL, color=NULL)+
    theme(text=element_text(size=16,face="bold"),axis.text.y=element_blank(), axis.ticks.y=element_blank())
ggsave("priors.png",plot=prio,width=5,height=5,units= "in", dpi=300)

raw <- read.csv2("raw_data_18112021.csv", dec=".",encoding= "latin1")

meta <- read.csv2("metadata4.csv")
data <- raw %>% select(all_of(meta$rowname[meta$keep==1])) %>% filter(Mortalitystatus== "ALIVE")
data$lab_nse0 <- as.numeric(data$lab_nse0)
dep_vars <- data %>% select(starts_with("qu_sympt"),qu_quality,qu_healthtoday)%>%colnames
forrest_labels<-read.csv2("forrest2.csv")

res<-rep(0,nrow(data))
for(i in 2:10){

  res<- cbind(res,difftime(dmy( data[[paste0("adm_delta",i)]] ),dmy( data$covid_diagndate ), units="days")*(data[[paste0("adm_delta",i,"type")]]!=1)*(data$adm_delta1type==1))
}

res <- res %>%t %>% as.data.frame %>% mutate(across(everything(),~min(.x[.x>0],na.rm=TRUE))) %>%t
res[res==Inf]<-0
data <- data%>%mutate(adm_delay=res[,1],
                      iw=isoweek(dmy(covid_diagndate))+as.numeric(dmy(covid_diagndate)-ymd("2021-01-03")>0)*53)
rm(res)
epidata <- read.csv2("Epidata.csv")
epidata <- epidata %>% mutate(patchar_gender=if_else(gender==1,0,1))
data <- left_join(data, epidata %>% select(patchar_gender, iw, naive_incidence, naive_prevalence))
data <- data %>% mutate(monthsaftercovid=as.numeric(round(difftime(ymd( qu_date ),ymd( covid_diagndate ), units= "days")/30)), late_follow_up=as.numeric(monthsaftercovid>8),
                        lab_ddhighest=lab_ddhighestcorrectedforsite4,
                        lab_dd1=lab_dd1correctedforsite4,
                        qu_verantwortung_yn = qu_verantwortung_haushalt%%2,
                        qu_einkommen_groesser = as.numeric(qu_einkommen_haushalt==1|qu_einkommen_haushalt==4),
                        qu_hat_partner = qu_status_partner%%7%%2,
                        qu_hs_abschluss = as.numeric( qu_abschluss>4 ),
                        qu_worse_quality = as.numeric( qu_quality>2 ),
                        qu_fear_yn = as.numeric( qu_sympt_fear>1),
                        haemodynamic_support = as.numeric((supe_hdtype___1+supe_hdtype___2+supe_hdtype___3)>0),
                        supe_resptype_7=as.numeric(supe_resptype==7),
                        estradiol_testosterone_ratio = if_else(is.finite(bb_estradiolfirst/bb_testosteronefirst),bb_estradiolfirst/bb_testosteronefirst,as.numeric(NA)),
                        neutro_lymphocyte_ratio = if_else(is.finite(lab_neutro1_number/lab_lympho1_lowest),lab_neutro1_number/lab_lympho1_lowest,as.numeric(NA)),
                        marital_status=as.factor(case_when(qu_status_partner==7 ~ "divorced or separated" , qu_status_partner==6 ~ "single", qu_status_partner==8 ~ "widowed", qu_status_partner<=5 ~ "married or in partnership" ,TRUE ~ "unknown"))
                        ) %>%
  select(-supe_hdtype___1,-supe_hdtype___2,-supe_hdtype___3,-lab_dd1correctedforsite4,-lab_ddhighestcorrectedforsite4)

data<-data %>% rowwise()%>%  mutate(all_sympt_acute=sum(c_across(matches("qu_symptoms_2___([^89]$|1[^0]|[^1].)")),na.rm=TRUE)+as.numeric(qu_symptoms_other!="")+str_count(qu_symptoms_other, ","),
                                    spec_sympt_acute= sum(c_across(matches("qu_symptoms_2___[1-5]$")),na.rm=TRUE),
                                    spec_any_acute=as.numeric(spec_sympt_acute>0),
                                    all_sympt_long=sum(c_across(matches("qu_sympt_type___(.$|1[^9]|[^1].)")),na.rm=TRUE)+as.numeric(qu_sympt_type_other!="")+str_count(qu_sympt_type_other, ","),
                                    spec_sympt_long=sum(c_across(matches("qu_sympt_type___[1267]$")),na.rm=TRUE),
                                    spec_any_long=as.numeric( spec_sympt_long>0 ),
                                    qu_gesamt_beschreibungen = mean(c_across(matches("qu_beschreibungen")),na.rm=TRUE),
                                    qu_komplikationen_ss = as.numeric(sum(c_across(matches("qu_komplikation_ss___[234567]")),na.rm=TRUE)>0),
                                    pre_existing_cardiovascular=as.numeric(sum(c_across(matches("pmh_knowncv___.$")),na.rm=TRUE)>0)) %>% ungroup
data<-data %>% rowwise()%>%
  mutate(all_comorbid=sum(sum(c_across(matches("qu_erkrankungen_1___[1-3]")),na.rm=TRUE), as.numeric(sum(c_across(matches("qu_herzerkrankungen___[^56]")),na.rm=TRUE)>0), as.numeric(sum(c_across(matches("qu_gefaesserkrankungen___[^67]")),na.rm=TRUE)>0), sum(c_across(matches("qu_erkrankungen_2___(([^9]$)|(1[^0]$)|([^1].$))")),na.rm=TRUE), qu_krebs_1,na.rm=TRUE)) %>% ungroup

data <- data %>% mutate(across(all_of(meta$rowname[meta$keep==1&meta$factor==1]),as.factor))
data$included <- as.numeric(!is.na(data$qu_sympt_ongoing))

gender_model <- glm(qu_geschlecht ~ qu_status_partner+ qu_abschluss+qu_einkommen_haushalt+qu_verantwortung_haushalt+qu_stress_1+qu_verantwortung_1+qu_beschreibungen_1+qu_beschreibungen_2+qu_beschreibungen_3+qu_beschreibungen_4+qu_beschreibungen_5+qu_beschreibungen_6+qu_beschreibungen_7+qu_beschreibungen_8+qu_beschreibungen_9+qu_beschreibungen_10, data=data, family="binomial")

data <- data %>% mutate(gender_score=predict(gender_model,data, type="response"))

ct_data <- data%>%
  filter(!is.na(gender_score))%>%
  select(where(~(is.numeric(.x)|is.factor(.x))&is.data.useful(.x)),-iw,-all_of(dep_vars),qu_sympt_ongoing,qu_sympt_fear,qu_quality)
lab_data <- data %>% filter(!is.na(lab_leuco1) & !is.na(qu_sympt_ongoing)) %>% select(where(~(is.numeric(.x)|is.factor(.x))&is.data.useful(.x)),-iw,-all_of(dep_vars),qu_sympt_ongoing,qu_sympt_fear)
bb_data <- data %>% filter(!is.na(bb_cortisolfirst) & !is.na(qu_sympt_ongoing)) %>% select(where(~(is.numeric(.x)|is.factor(.x))&is.data.useful(.x)),-iw,-all_of(dep_vars),qu_sympt_ongoing,qu_sympt_fear)

long1 <- glm(qu_sympt_ongoing~(as.factor( patcher_site )+(qu_quality>2)+naive_prevalence)*qu_geschlecht,data=ct_data,family="binomial")
long2 <- glm(qu_sympt_ongoing~(as.factor( patcher_site )+(qu_quality>2)+naive_prevalence)*qu_zuege_geschlecht_1,data=ct_data,family="binomial")
long3 <- glm(qu_sympt_ongoing~(as.factor( patcher_site )+(qu_quality>2)+naive_prevalence)*gender_score,data=ct_data,family="binomial")
write.xlsx2(compareGLM(long1, long2, long3),file="basic_models.xlsx")

long1_spec <- glm(spec_any_long~(as.factor( patcher_site )+(qu_quality>2)+naive_prevalence)*qu_geschlecht,data=ct_data,family="binomial")
long2_spec <- glm(spec_any_long~(as.factor( patcher_site )+(qu_quality>2)+naive_prevalence)*qu_zuege_geschlecht_1,data=ct_data,family="binomial")
long3_spec <- glm(spec_any_long~(as.factor( patcher_site )+(qu_quality>2)+naive_prevalence)*gender_score,data=ct_data,family="binomial")
write.xlsx2(compareGLM(long1_spec, long2_spec, long3_spec),file="basic_models_specific.xlsx")

write.xlsx2(exp(cbind(coef(long1),confint(long1))),sheetName="Sex unspecific",file="basic_models_confidence.xlsx")
write.xlsx2(exp(cbind(coef(long2),confint(long2))),sheetName="Self-assesesd unspeific",file="basic_models_confidence.xlsx",append=TRUE)
write.xlsx2(exp(cbind(coef(long3),confint(long3))),sheetName="Gender Score unspecific",file="basic_models_confidence.xlsx",append=TRUE)
write.xlsx2(exp(cbind(coef(long1_spec),confint(long1_spec))),sheetName="Sex specific",file="basic_models_confidence.xlsx",append=TRUE)
write.xlsx2(exp(cbind(coef(long2_spec),confint(long2_spec))),sheetName="Self-assessed specific",file="basic_models_confidence.xlsx",append=TRUE)
write.xlsx2(exp(cbind(coef(long3_spec),confint(long3_spec))),sheetName="Gender Score specific",file="basic_models_confidence.xlsx",append=TRUE)

minimal1 <- glm(qu_sympt_ongoing~patchar_gender,data=ct_data,family="binomial")

minimal2 <- glm(qu_sympt_ongoing~gender_score,data=ct_data,family="binomial")
minimal3 <-  glm(qu_sympt_ongoing~gender_score+patchar_gender,data=ct_data,family="binomial")
minimal4<- glm(qu_sympt_ongoing~poly(adm_age,2)+all_comorbid+patchar_gender,data=ct_data,family="binomial")

minimal5 <- glm(qu_sympt_ongoing~poly(adm_age,2)+all_comorbid+gender_score,data=ct_data,family="binomial")
minimal6 <-  glm(qu_sympt_ongoing~poly(adm_age,2)+all_comorbid+gender_score+patchar_gender,data=ct_data,family="binomial")

write.xlsx2(compareGLM(minimal1, minimal2, minimal3, minimal4, minimal5, minimal6),file="minimal_models.xlsx")

write.xlsx2(exp(cbind(coef(minimal1),confint(minimal1))),sheetName="Sex ",file="minimal_models_confidence.xlsx")
write.xlsx2(exp(cbind(coef(minimal2),confint(minimal2))),sheetName="Gender Score",file="minimal_models_confidence.xlsx",append=TRUE)
write.xlsx2(exp(cbind(coef(minimal3),confint(minimal3))),sheetName="Sex and Gender Score ",file="minimal_models_confidence.xlsx",append=TRUE)
write.xlsx2(exp(cbind(coef(minimal4),confint(minimal4))),sheetName="Adjusted Sex ",file="minimal_models_confidence.xlsx",append=TRUE)
write.xlsx2(exp(cbind(coef(minimal5),confint(minimal5))),sheetName="Adjusted Gender Score",file="minimal_models_confidence.xlsx",append=TRUE)
write.xlsx2(exp(cbind(coef(minimal6),confint(minimal6))),sheetName="Adjusted Sex and Gender Score ",file="minimal_models_confidence.xlsx",append=TRUE)


ct_models <- create_models(na.omit(ct_data),"qu_sympt_ongoing",
                           colnames(ct_data%>%select(-qu_sympt_ongoing,-matches("long"),-matches("fear"),-matches("quality"),-pmh_comorbid___9999)),
                           c("patchar_gender","gender_score"))
ct_models_comp <- compare_models_at(ct_models)
#model 4 is best
ct_models[["stanreg_models"]][["model4"]] <- stan_glm(qu_sympt_ongoing ~ pmh_cvrf___4 + covid_symp___2 + med_covid___9999 + qu_erkrankungen_2___9 + qu_stress_1 + all_sympt_acute + spec_sympt_acute + as.numeric(qu_abschluss == 3) + as.numeric(qu_abschluss == 4) + patchar_gender:as.numeric(qu_status_partner == 8) + covid_symp___3:gender_score + covid_symp___6:gender_score,data=na.omit(ct_data),family=binomial(link= "logit"),prior=lasso(df=1,autoscale=TRUE), prior_intercept=normal(0,1), cores =4, seed=1234)


ct_models_spec <- create_models(na.omit(ct_data),"spec_any_long",
                           colnames(ct_data%>%select(-qu_sympt_ongoing,-matches("long"),-matches("fear"),-matches("quality"),-pmh_comorbid___9999)),
                           c("patchar_gender","gender_score"))
ct_models_spec_comp <- compare_models_at(ct_models_spec)
#model 2 is best
ct_models_spec[["stanreg_models"]][["model2"]]<-stan_glm(spec_any_long ~ covid_symp___2 + covid_compl___1 + med_adm___9999 +  med_covid___9999 + qu_weight + qu_raucher + qu_herzerkrankungen___6 +  qu_erkrankungen_2___9 + qu_stress_1 + qu_beschreibungen_1 +  all_sympt_acute + spec_sympt_acute + as.numeric(qu_status_partner ==  2) + patchar_gender:as.numeric(qu_begruessungsritual == 4) + patchar_gender:as.numeric(qu_begruessungsritual ==  5) + patchar_gender:as.numeric(qu_status_partner == 8) + patchar_gender:as.numeric(qu_einkommen_haushalt ==  4) + patchar_gender:qu_verantwortung_1 + covid_symp___2:gender_score +  covid_symp___6:gender_score,data=na.omit(ct_data),family=binomial(link= "logit"),prior=lasso(df=1,autoscale=TRUE), prior_intercept=normal(0,1), cores =4, seed=1234)


ct_models_fear <- create_models(na.omit(ct_data),"qu_fear_yn",
                           colnames(ct_data%>%select(-qu_sympt_ongoing,-matches("long"),-matches("fear"),-matches("quality"),-pmh_comorbid___9999)),
                           c("patchar_gender","gender_score"))
ct_models_fear_comp <- compare_models_at(ct_models_fear)
#model 2 is best
ct_models_fear[["stanreg_models"]][["model2"]]<-stan_glm(qu_fear_yn ~ pmh_cvrf___9999 + adm_age + covid_diagnage + qu_height + qu_erkrankungen_1___2 + qu_erkrankungen_1___5 + qu_alleinerziehend + qu_stress_1 + qu_beschreibungen_2 + qu_beschreibungen_5 + qu_beschreibungen_8 + all_sympt_acute + as.numeric(qu_begruessungsritual == 4) + as.numeric(qu_abschluss == 3) + as.numeric(qu_einkommen_haushalt == 3) + patchar_gender:covid_symp___4 + patchar_gender:as.numeric(qu_status_partner == 7) + as.numeric(qu_begruessungsritual == 5):gender_score + adm_delay:gender_score,data=na.omit(ct_data),family=binomial(link= "logit"),prior=lasso(df=1,autoscale=TRUE), prior_intercept=normal(0,1), cores =4, seed=1234)

lab_data2 <- lab_data %>% select(where(~length(na.omit(.x))>575),gender_score) %>% na.omit
lab_models2 <- create_models(lab_data2,"qu_sympt_ongoing",
                             c( all.vars(ct_models[["stanreg_models"]][["model4"]]$formula[-2]),grep("^lab|stat|supe|saps|sofa|mach",colnames(lab_data2),value=TRUE)),
                             c("patchar_gender","gender_score"),
                             normal(0,1)
                             )
lab_models_comp2 <- compare_models_at(lab_models2)
                                        #model 9 better than 0

lab_models2[["stanreg_models"]][["model9"]]<-stan_glm(qu_sympt_ongoing ~ qu_erkrankungen_2___9 + qu_stress_1 + all_sympt_acute + covid_symp___3 + lab_leuco1 + lab_tc1 + lab_bili1 + lab_nalowest + lab_leucohighest + lab_tclowest + stat_spo2 + as.numeric(qu_status_partner == 8) + qu_stress_1:patchar_gender + patchar_gender:covid_symp___6 + patchar_gender:lab_hb1 + patchar_gender:lab_leuco1 + patchar_gender:lab_neutro1_number + patchar_gender:lab_tc1 + patchar_gender:lab_alat1 + patchar_gender:lab_tchighest + patchar_gender:lab_kreahighest + gender_score:lab_hb1 + gender_score:lab_tc1 + gender_score:lab_alat1 + gender_score:lab_nalowest + gender_score:lab_hbhighest + gender_score:lab_tclowest + gender_score:stat_spo2 + gender_score:mach_respoxindex,data=lab_data2,family=binomial(link= "logit"),prior=normal(0,1), prior_intercept=normal(0,1), cores =4, seed=1234)

lab_models_spec2 <- create_models(lab_data2,"spec_any_long",
                                  c(all.vars(ct_models_spec[["stanreg_models"]][["model2"]]$formula[-2]),grep("^lab|stat|supe|saps|sofa|mach",colnames(lab_data2),value=TRUE)),
                                  c("patchar_gender","gender_score"),
                                  normal(0,1))
lab_models_spec_comp2 <- compare_models_at(lab_models_spec2)
                                        #model 8 better than 0

lab_models_spec2[["stanreg_models"]][["model8"]]<-stan_glm(temp_form,data=lab_data2,family=binomial(link= "logit"),prior=normal(0,1), prior_intercept=normal(0,1), cores =4, seed=1234)

allall <- data %>% filter(!is.na(qu_sympt_ongoing)) %>% summarize(across(everything(),col_gen)) %>% t %>% as.data.frame %>% rownames_to_column
write.xlsx2(allall,"Overall_data.xlsx")

no_gender_long <- data %>%
  filter(!is.na(qu_sympt_ongoing)) %>%
  group_by(qu_sympt_ongoing) %>%
  summarize(across(everything(),col_gen)) %>% t %>% as.data.frame %>% rownames_to_column
no_gender_long_p <- data %>%
  filter(!is.na(qu_sympt_ongoing)) %>%
  summarize(across(everything(), ~col_test(.x,qu_sympt_ongoing==1,qu_sympt_ongoing==0))) %>% t%>% as.data.frame %>% rownames_to_column

write.xlsx2(left_join(no_gender_long, no_gender_long_p,by= "rowname"),file= "No_gender_long.xlsx",sheetName= "No Gender Long")

bias <- data %>%
  group_by(included) %>%
  summarize(across(everything(),col_gen)) %>% t %>% as.data.frame %>% rownames_to_column
bias_p <- data %>%
  summarize(across(everything(), ~col_test(.x,included==1,included==0))) %>% t%>% as.data.frame %>% rownames_to_column

write.xlsx2(left_join(bias, bias_p,by= "rowname"),file= "Bias.xlsx",sheetName= "Bias")

no_gender_long_spec <- data %>%
  filter(!is.na(qu_sympt_ongoing)) %>%
  group_by(spec_any_long) %>%
  summarize(across(everything(),col_gen)) %>% t %>% as.data.frame %>% rownames_to_column
no_gender_long_p_spec <- data %>%
  filter(!is.na(qu_sympt_ongoing)) %>%
  summarize(across(everything(), ~col_test(.x,spec_any_long==1,spec_any_long==0))) %>% t%>% as.data.frame %>% rownames_to_column

write.xlsx2(left_join(no_gender_long_spec, no_gender_long_p_spec,by= "rowname"),file= "No_gender_long_specific.xlsx",sheetName= "No Gender Long Specific")


baselines <- data %>% filter(!is.na(qu_sympt_ongoing)) %>% group_by(qu_sympt_ongoing,patchar_gender) %>% summarize(across(everything(),col_gen)) %>% t %>% as.data.frame %>% rownames_to_column
base_long <- data %>% filter(!is.na(qu_sympt_ongoing)) %>% summarize(across(everything(), ~col_test(.x,qu_sympt_ongoing==1&patchar_gender==0,qu_sympt_ongoing==1&patchar_gender==1))) %>% t%>% as.data.frame %>% rownames_to_column

base_nolong <- data %>% filter(!is.na(qu_sympt_ongoing)) %>% summarize(across(everything(), ~col_test(.x,qu_sympt_ongoing==0&patchar_gender==0,qu_sympt_ongoing==0&patchar_gender==1))) %>% t%>% as.data.frame %>% rownames_to_column

base_men <- data %>% filter(!is.na(qu_sympt_ongoing)) %>% summarize(across(everything(), ~col_test(.x,qu_sympt_ongoing==0&patchar_gender==0,qu_sympt_ongoing==1&patchar_gender==0))) %>% t%>% as.data.frame %>% rownames_to_column

base_women <- data %>% filter(!is.na(qu_sympt_ongoing)) %>% summarize(across(everything(), ~col_test(.x,qu_sympt_ongoing==0&patchar_gender==1,qu_sympt_ongoing==1&patchar_gender==1))) %>% t%>% as.data.frame %>% rownames_to_column

write.xlsx2(left_join(baselines, base_nolong,by= "rowname")%>% left_join( base_long,by= "rowname" ) %>%left_join( base_men,by= "rowname" ) %>%left_join( base_women,by= "rowname" ) ,file= "Baseline.xlsx",sheetName= "Full Baselines")


baselines_spec <- data %>% filter(!is.na(qu_sympt_ongoing)) %>% group_by(spec_any_long,patchar_gender) %>% summarize(across(everything(),col_gen)) %>% t %>% as.data.frame %>% rownames_to_column

base_long_spec <- data %>% filter(!is.na(qu_sympt_ongoing)) %>% summarize(across(everything(), ~col_test(.x,spec_any_long==1&patchar_gender==0,spec_any_long==1&patchar_gender==1))) %>% t%>% as.data.frame %>% rownames_to_column

base_nolong_spec <- data %>% filter(!is.na(qu_sympt_ongoing)) %>% summarize(across(everything(), ~col_test(.x,spec_any_long==0&patchar_gender==0,spec_any_long==0&patchar_gender==1))) %>% t%>% as.data.frame %>% rownames_to_column

base_men_spec <- data %>% filter(!is.na(qu_sympt_ongoing)) %>% summarize(across(everything(), ~col_test(.x,spec_any_long==1&patchar_gender==0,spec_any_long==0&patchar_gender==0))) %>% t%>% as.data.frame %>% rownames_to_column

base_women_spec <- data %>% filter(!is.na(qu_sympt_ongoing)) %>% summarize(across(everything(), ~col_test(.x,spec_any_long==1&patchar_gender==1,spec_any_long==0&patchar_gender==1))) %>% t%>% as.data.frame %>% rownames_to_column


write.xlsx2(left_join(baselines_spec, base_nolong_spec,by= "rowname")%>% left_join( base_long_spec,by= "rowname" ) %>%left_join( base_men_spec,by= "rowname" ) %>% left_join( base_women_spec,by= "rowname" ),file= "Baseline_spec.xlsx",sheetName= "Full Baselines Spec")

write.xlsx2(ct_models[["stanreg_models"]][["model4"]]$stan_summary %>% exp %>% as.data.frame %>%rownames_to_column %>% filter(!(rowname %in% c("mean_PPD","log-posterior","(Intercept)"))&sign(`10%`)==sign(`90%`))%>%arrange(`10%`)%>%left_join(forrest_labels,by=c("rowname"= "variable"))%>% mutate(description=factor(description, levels=description)),
            file= "Bayes_lasso_models.xlsx",sheetName= "Overall Any")
write.xlsx2(ct_models_spec[["stanreg_models"]][["model2"]]$stan_summary %>% exp %>% as.data.frame %>%rownames_to_column %>% filter(!(rowname %in% c("mean_PPD","log-posterior","(Intercept)"))&sign(`10%`)==sign(`90%`))%>%arrange(`10%`)%>%left_join(forrest_labels,by=c("rowname"= "variable"))%>% mutate(description=factor(description,levels=description)),
            file= "Bayes_lasso_models.xlsx",sheetName= "Overall Specific",append = TRUE)
write.xlsx2(ct_models_fear[["stanreg_models"]][["model2"]]$stan_summary %>% exp %>% as.data.frame %>%rownames_to_column %>% filter(!(rowname %in% c("mean_PPD","log-posterior","(Intercept)"))&sign(`10%`)==sign(`90%`))%>%arrange(`10%`)%>%left_join(forrest_labels,by=c("rowname"= "variable"))%>% mutate(description=factor(description,levels=description)),
            file= "Bayes_lasso_models.xlsx",sheetName= "Fear Any",append = TRUE)
write.xlsx2(lab_models2[["stanreg_models"]][["model9"]]$stan_summary %>% exp %>% as.data.frame %>%rownames_to_column %>% filter(!(rowname %in% c("mean_PPD","log-posterior","(Intercept)"))&sign(`10%`)==sign(`90%`))%>%arrange(`10%`)%>%left_join(forrest_labels,by=c("rowname"= "variable"))%>% mutate(description=factor(description, levels=description)),
            file= "Bayes_lasso_models.xlsx",sheetName= "Lab Any",append = TRUE)
write.xlsx2(lab_models_spec2[["stanreg_models"]][["model8"]]$stan_summary %>% exp %>% as.data.frame %>%rownames_to_column %>% filter(!(rowname %in% c("mean_PPD","log-posterior","(Intercept)"))&sign(`10%`)==sign(`90%`))%>%arrange(`10%`)%>%left_join(forrest_labels,by=c("rowname"= "variable"))%>% mutate(description=factor(description, levels=description)),
            file= "Bayes_lasso_models.xlsx",sheetName= "Lab Specific",append = TRUE)

no_gender_fear <- data %>%
  filter(!is.na(qu_sympt_fear)) %>%
  group_by(qu_fear_yn) %>%
  summarize(across(everything(),col_gen)) %>% t %>% as.data.frame %>% rownames_to_column
no_gender_fear_p <- data %>%
   filter(!is.na(qu_sympt_fear)) %>%
  summarize(across(everything(), ~col_test(.x,qu_fear_yn==1,qu_fear_yn==0))) %>% t%>% as.data.frame %>% rownames_to_column

write.xlsx2(left_join(no_gender_fear, no_gender_fear_p,by= "rowname"),file= "No_gender_fear.xlsx",sheetName= "No Gender Fear")

baselines_fear <- data %>%
  filter(!is.na(qu_sympt_fear)) %>%
  group_by(qu_fear_yn,patchar_gender) %>%
  summarize(across(everything(),col_gen)) %>% t %>% as.data.frame %>% rownames_to_column
base_fear <- data %>%
  filter(!is.na(qu_sympt_fear)) %>%
  summarize(across(everything(), ~col_test(.x,qu_fear_yn==1&patchar_gender==0,qu_fear_yn==1&patchar_gender==1))) %>% t%>% as.data.frame %>% rownames_to_column

base_nofear <- data %>%
  filter(!is.na(qu_sympt_fear)) %>%
  summarize(across(everything(), ~col_test(.x,qu_fear_yn==0&patchar_gender==0,qu_fear_yn==0&patchar_gender==1))) %>% t%>% as.data.frame %>% rownames_to_column

write.xlsx2(left_join(baselines_fear, base_nofear,by= "rowname")%>% left_join( base_fear,by= "rowname" ),file= "Baseline_fear.xlsx",sheetName= "Full Baselines Fear")

symptom_labels <- read.csv2("qu_sypmt_type_cg.csv",sep= ",")
symptoms <- ggplot(left_join(raw %>% filter (qu_sympt_ongoing==1) %>% select(patchar_gender, starts_with("qu_sympt_type__")) %>% group_by(patchar_gender)%>% summarize(across(everything(),sum)) %>% pivot_longer(cols=!patchar_gender, values_to="n"),raw %>% filter (qu_sympt_ongoing==1) %>% select(patchar_gender, starts_with("qu_sympt_type__")) %>% group_by(patchar_gender)%>% summarize(across(everything(),~sum(.x)/length(.x)*100)) %>% pivot_longer(cols=!patchar_gender, values_to="perc"))%>%left_join(symptom_labels) %>% arrange(perc) %>% mutate(description=factor(description,levels=unique( description ))) %>% filter(as.integer(description)>17)) +
  geom_bar(aes(y=description,x=perc,fill=as.factor(patchar_gender)),color="grey50",alpha=0.7,stat= "identity",position=position_dodge())+
  geom_text(aes(y=description,x=perc+5.5,fill=as.factor(patchar_gender),label=paste0(round(perc,2),"% (n=",n,")")),fontface="bold", position=position_dodge(0.9),size=2)+
  scale_fill_manual(name = "Sex",values=c("0"= "blue", "1"= "tomato"),labels=c("0"= "Men", "1"= "Women"))+
  scale_x_continuous(name= "Patients (%) with any persistent symptom",limits=c(0,55))+
  labs(y= "")+
  theme_classic() +
  theme(text=element_text(size=11,face="bold"))

ggsave("Symptoms.png",plot=symptoms,width=5,height=5,units= "in", dpi=300)

genders <- ggplot(data,aes(x=gender_score,fill=as.factor(patchar_gender))) +
  geom_histogram(alpha=0.7,position="identity",color="grey50")+
  labs(x= "Gender score", y = "Number of patients")+
  scale_fill_manual(values=c("0"= "blue", "1"= "tomato"),labels=c("0"= "Men", "1"= "Women"), name= "Sex")+
  theme_classic()+
  theme(text=element_text(size=11,face="bold"))
ggsave("Gender_score.png",plot=genders,width=5,height=5,units= "in", dpi=300)

gl<-ggplot(data %>% filter(!is.na(qu_sympt_ongoing)),aes(x=gender_score,color=as.factor(patchar_gender), linetype=as.factor(qu_sympt_ongoing), fill=NULL))+
  stat_density(alpha=0.7,geom="line",position="identity")+
  scale_linetype_manual(name = "Any persistent symptom", labels=c("0"= "No", "1"= "Yes"),values=c("0"=1,"1"=2))+
  scale_color_manual(name = "Sex",values=c("0"= "blue", "1"= "tomato"),labels=c("0"= "Men", "1"= "Women"))+
  labs(x= "Gender score", y = "Density of patients")+
  guides(linetype=guide_legend(order=2),color=guide_legend(order=1))+
  theme_classic()+
  theme(text=element_text(size=11,face="bold"))


ggsave("Gender_score_long_covid.png",plot=gl,width=5,height=5,units= "in", dpi=300)

gl_tertile<-ggplot(data %>% filter(!is.na(qu_sympt_ongoing) & !is.na(gender_score))%>%mutate(gs=ntile(gender_score,3))%>%group_by(gs, patchar_gender,qu_sympt_ongoing)%>%summarize(all=n()),aes(x=as.factor(patchar_gender),y=all,fill=as.factor(patchar_gender):as.factor(qu_sympt_ongoing)))+
  geom_bar(stat="identity",alpha=0.7,color="grey50",position="stack")+
  geom_hline(yintercept=0)+
  facet_wrap(~gs,labeller=labeller(gs=c("1"= "First tertile","2"= "Second tertile", "3"= "Third tertile")),strip.position= "bottom")+
  scale_fill_manual(name = "Sex & symptoms",values=c("0:0"= "blue4","0:1"= "blue", "1:0"= "tomato4", "1:1"= "tomato"),labels=c("0:0"= "Men, no persistent symptoms","0:1"= "Men, any persistent symptoms" , "1:0"= "Women, no persistent symptoms", "1:1"= "Women, any persistent symptoms"))+
  labs(x= "Gender score", y = "Number of patients")+
  ylim(0,750)+
  theme_classic()+
  theme(text=element_text(size=11,face="bold"), legend.text=element_text(size=7,face="bold"),strip.text= element_text(vjust=3),strip.background=element_blank(),axis.line.x=element_blank(),axis.text.x=element_blank(),axis.ticks.x=element_blank())


ggsave("Gender_score_long_covid_tertile.png",plot=gl_tertile,width=5.5,height=5.5,units= "in", dpi=300)

gls<-ggplot(data %>% filter(!is.na(qu_sympt_ongoing)),aes(x=gender_score,color=as.factor(patchar_gender), linetype=as.factor(spec_any_long), fill=NULL))+
  stat_density(alpha=0.7,geom="line",position="identity")+
  scale_linetype_manual(name = "Specific persistent symptoms", labels=c("0"= "No", "1"= "Yes"),values=c("0"=1,"1"=2))+
  scale_color_manual(name = "Sex",values=c("0"= "blue", "1"= "tomato"),labels=c("0"= "Men", "1"= "Women"))+
  labs(x= "Gender score", y = "Density of patients")+
  guides(linetype=guide_legend(order=2),color=guide_legend(order=1))+
  theme_classic()+
  theme(text=element_text(size=11,face="bold"))

ggsave("Gender_score_long_covid_specific.png",plot=gls,width=5,height=5,units= "in", dpi=300)


gc<-ggplot(data %>% filter(!is.na(qu_sympt_ongoing) & !is.na(bb_cortisolfirst)&!is.na(gender_score))%>%mutate(gs=ntile(gender_score,3))%>% group_by(gs,qu_sympt_ongoing) %>% summarize(m=mean(bb_cortisolfirst),s=sd(bb_cortisolfirst)/sqrt(n())),aes(x=as.factor(gs), y=m,ymin=m-s,ymax=m+s,fill=as.factor(qu_sympt_ongoing)))+
  geom_bar(stat= "identity",position=position_dodge())+
  geom_errorbar(position=position_dodge(0.9),width=0.5)+
  labs(x= "Gender score", y = "Cortisol level in nmol/L")+
  scale_x_discrete(labels=c("First tertile","Second tertile", "Third tertile"))+
  scale_fill_manual(values=c("0"= "darkgreen", "1"= "orange"),labels=c("0"= "No", "1"= "Yes"), name= "Any persistent symptom")+
  theme_classic()+
  theme(text=element_text(size=11,face="bold"))

ggsave("Gender_score_cortisol.png",plot=gc,width=5,height=5,units= "in", dpi=300)

spo2<-ggplot(data %>% filter(!is.na(qu_sympt_ongoing) & !is.na(stat_spo2)&!is.na(gender_score))%>%mutate(gs=ntile(gender_score,3))%>% group_by(gs,qu_sympt_ongoing) %>% summarize(m=mean(stat_spo2),s=sd(stat_spo2)/sqrt(n())),aes(x=as.factor(gs), y=m,ymin=m-s,ymax=m+s,fill=as.factor(qu_sympt_ongoing)))+
  geom_bar(stat= "identity",position=position_dodge())+
  geom_errorbar(position=position_dodge(0.9),width=0.5)+
  labs(x= "Gender score", y = "First day SpO2")+
  coord_cartesian(ylim=c(90,100))+
  scale_x_discrete(labels=c("First tertile","Second tertile", "Third tertile"))+
  scale_fill_manual(values=c("0"= "darkgreen", "1"= "orange"),labels=c("0"= "No", "1"= "Yes"), name= "Any persistent symptom")+
  theme_classic()+
  theme(text=element_text(size=11,face="bold"))

ggsave("Gender_score_spo2.png",plot=spo2,width=5,height=5,units= "in", dpi=300)

sod<-ggplot(data %>% filter(!is.na(qu_sympt_ongoing) & !is.na(lab_nalowest)&!is.na(gender_score))%>%mutate(gs=ntile(gender_score,3))%>% group_by(gs,qu_sympt_ongoing) %>% summarize(m=mean(lab_nalowest),s=sd(lab_nalowest)/sqrt(n())),aes(x=as.factor(gs), y=m,ymin=m-s,ymax=m+s,fill=as.factor(qu_sympt_ongoing)))+
  geom_bar(stat= "identity",position=position_dodge())+
  geom_errorbar(position=position_dodge(0.9),width=0.5)+
  coord_cartesian(ylim=c(125,140))+
  labs(x= "Gender score", y = "Lowest sodium level during acute illness (mmol/L)")+
  scale_x_discrete(labels=c("First tertile","Second tertile", "Third tertile"))+
  scale_fill_manual(values=c("0"= "darkgreen", "1"= "orange"),labels=c("0"= "No", "1"= "Yes"), name= "Any persistent symptom")+
  theme_classic()+
  theme(text=element_text(size=11,face="bold"))

ggsave("Gender_score_sod.png",plot=sod,width=5,height=5,units= "in", dpi=300)

pc<-ggplot(data %>% filter(!is.na(qu_sympt_ongoing) & !is.na(bb_cortisolfirst))%>%group_by(patchar_gender,qu_sympt_ongoing) %>% summarize(m=mean(bb_cortisolfirst),s=sd(bb_cortisolfirst)/sqrt(n())),aes(x=as.factor(qu_sympt_ongoing), y=m,ymin=m-s,ymax=m+s,fill=as.factor(patchar_gender)))+
  geom_bar(stat= "identity",position=position_dodge(),alpha=0.7,color= "grey50")+
  geom_errorbar(position=position_dodge(0.9),width=0.5)+
  labs(x= "Any persistent symptom", y = "Cortisol level in nmol/L")+
  scale_x_discrete(labels=c("0"="No","1"= "Yes"))+
  scale_fill_manual(values=c("0"= "blue", "1"= "tomato"),labels=c("0"= "Men", "1"= "Women"), name= "Sex")+
  theme_classic()+
  theme(text=element_text(size=11,face="bold"))


ggsave("Patchar_gender_cortisol.png",plot=pc,width=5,height=5,units= "in", dpi=300)

ps<-ggplot(data %>% filter(!is.na(qu_sympt_ongoing) & !is.na(qu_stress_1))%>%group_by(patchar_gender,qu_sympt_ongoing) %>% summarize(m=mean(qu_stress_1),s=sd(qu_stress_1)/sqrt(n())),aes(x=as.factor(qu_sympt_ongoing), y=m,ymin=m-s,ymax=m+s,fill=as.factor(patchar_gender)))+
  geom_bar(stat= "identity",position=position_dodge(),alpha=0.7, color= "grey50")+
  geom_errorbar(position=position_dodge(0.9),width=0.5)+
  labs(x= "Any persistent symptom", y = "Domestic stress level (1-10)")+
  scale_x_discrete(labels=c("0"="No","1"= "Yes"))+
  scale_fill_manual(values=c("0"= "blue", "1"= "tomato"),labels=c("0"= "Men", "1"= "Women"), name= "Sex")+
  theme_classic()+
  theme(text=element_text(size=11,face="bold"))


ggsave("Patchar_gender_stress.png",plot=ps,width=5,height=5,units= "in", dpi=300)

comorb<-ggplot(data %>% filter(!is.na(qu_sympt_ongoing) & !is.na(all_comorbid))%>%group_by(patchar_gender,qu_sympt_ongoing) %>% summarize(m=mean(all_comorbid),s=sd(all_comorbid)/sqrt(n())),aes(x=as.factor(qu_sympt_ongoing), y=m,ymin=m-s,ymax=m+s,fill=as.factor(patchar_gender)))+
  geom_bar(stat= "identity",position=position_dodge(),alpha=0.7, color= "grey50")+
  geom_errorbar(position=position_dodge(0.9),width=0.5)+
  labs(x= "Any persistent symptom", y = "Number of comorbidities")+
  scale_x_discrete(labels=c("0"="No","1"= "Yes"))+
  scale_fill_manual(values=c("0"= "blue", "1"= "tomato"),labels=c("0"= "Men", "1"= "Women"), name= "Sex")+
  theme_classic()+
  theme(text=element_text(size=11,face="bold"))


ggsave("Patchar_gender_comorb.png",plot=comorb,width=5,height=5,units= "in", dpi=300)

dp<-ggplot(data %>% filter(!is.na(qu_sympt_ongoing) & !is.na(qu_status_partner))%>%group_by(patchar_gender,qu_sympt_ongoing) %>% summarize(m=sum(as.numeric(qu_status_partner==8))/n()*100),aes(x=as.factor(qu_sympt_ongoing), y=m,fill=as.factor(patchar_gender)))+
  geom_bar(stat= "identity",position=position_dodge(),alpha=0.7,color= "grey50")+
  labs(x= "Any persistent symptom", y = "Individuals being widowed (%)")+
  scale_x_discrete(labels=c("0"="No","1"= "Yes"))+
  scale_fill_manual(values=c("0"= "blue", "1"= "tomato"),labels=c("0"= "Men", "1"= "Women"), name= "Sex")+
  theme_classic()+
  theme(text=element_text(size=11,face="bold"))


ggsave("Patchar_gender_deceasedpartner.png",plot=dp,width=5,height=5,units= "in", dpi=300)

divorsed<-ggplot(data %>% filter(!is.na(qu_sympt_ongoing) & !is.na(marital_status))%>%group_by(patchar_gender,qu_sympt_ongoing) %>% summarize(m=sum(as.numeric(marital_status== "divorced or separated"))/n()*100),aes(x=as.factor(qu_sympt_ongoing), y=m,fill=as.factor(patchar_gender)))+
  geom_bar(stat= "identity",position=position_dodge(),alpha=0.7,color= "grey50")+
  labs(x= "Any persistent symptom", y = "Individuals living divorced or separated (%)")+
  scale_x_discrete(labels=c("0"="No","1"= "Yes"))+
  scale_fill_manual(values=c("0"= "blue", "1"= "tomato"),labels=c("0"= "Men", "1"= "Women"), name= "Sex")+
  theme_classic()+
  theme(text=element_text(size=11,face="bold"))


ggsave("Patchar_gender_divorsedsep.png",plot=divorsed,width=5,height=5,units= "in", dpi=300)

lo<-ggplot(data %>% filter(!is.na(qu_sympt_ongoing) & !is.na(qu_einkommen_haushalt))%>%group_by(patchar_gender,qu_sympt_ongoing) %>% summarize(m=sum(as.numeric(qu_einkommen_haushalt==4))/n()*100),aes(x=as.factor(qu_sympt_ongoing), y=m,fill=as.factor(patchar_gender)))+
  geom_bar(stat= "identity",position=position_dodge(),alpha=0.7,color= "grey50")+
  labs(x= "Any persistent symptom", y = "Individuals living alone (%)")+
  scale_x_discrete(labels=c("0"="No","1"= "Yes"))+
  scale_fill_manual(values=c("0"= "blue", "1"= "tomato"),labels=c("0"= "Men", "1"= "Women"), name= "Sex")+
  theme_classic()+
  theme(text=element_text(size=11,face="bold"))


ggsave("Patchar_gender_livingalone.png",plot=lo,width=5,height=5,units= "in", dpi=300)


forrest <- ggplot(ct_models[["stanreg_models"]][["model4"]]$stan_summary %>% as.data.frame %>%rownames_to_column %>% filter(!(rowname %in% c("mean_PPD","log-posterior","(Intercept)"))&sign(`10%`)==sign(`90%`))%>%arrange(`10%`)%>%left_join(forrest_labels,by=c("rowname"= "variable"))%>% mutate(description=factor(description, levels=description)),aes(y=description,xmin=exp( `10%` ), x=exp( `50%` ),xmax=exp( `90%` )))+
  geom_point()+
  geom_errorbarh(height=0.1)+
  scale_x_continuous(limits=c(0.4,7.5),breaks=c(0.4,0.6,1,1.5,2.5,4.5,7.5),trans="log10")+
  geom_vline(xintercept=1,color="grey",show.legend=0)+labs(y= "",x= "Odds")+  theme_classic()+

  theme(text=element_text(size=11,face="bold"))

ggsave("Bayes_lasso_hpd.png",plot=forrest,width=7,height=7,units= "in", dpi=300)

forrest_spec <- ggplot(ct_models_spec[["stanreg_models"]][["model2"]]$stan_summary %>% as.data.frame %>%rownames_to_column %>% filter(!(rowname %in% c("mean_PPD","log-posterior","(Intercept)"))&sign(`10%`)==sign(`90%`))%>%arrange(`10%`)%>%left_join(forrest_labels,by=c("rowname"= "variable"))%>% mutate(description=factor(description,levels=description)),aes(y=description,xmin=exp(`10%` ),x=exp( `50%` ),xmax=exp( `90%` )))+
  scale_x_continuous(limits=c(0.4,7.5),breaks=c(0.4,0.6,1,1.5,2.5,4.5,7.5),trans="log10")+
  geom_point()+
  geom_errorbarh(height=0.1)+
  geom_vline(xintercept=1,color="grey",show.legend=0)+
  labs(y= "",x= "Odds")+theme_classic()+
  theme(text=element_text(size=11,face="bold"))

ggsave("Bayes_lasso_hpd_spec.png",plot=forrest_spec,width=7,height=7,units= "in", dpi=300)

forrest_fear <- ggplot(ct_models_fear[["stanreg_models"]][["model2"]]$stan_summary %>% as.data.frame %>%rownames_to_column %>% filter(!(rowname %in% c("mean_PPD","log-posterior","(Intercept)"))&sign(`10%`)==sign(`90%`))%>%arrange(`10%`)%>%left_join(forrest_labels,by=c("rowname"= "variable"))%>% mutate(description=factor(description,levels=description)),aes(y=description,xmin=exp(`10%`),x=exp(`50%`),xmax=exp(`90%`)))+
  scale_x_continuous(limits=c(0.4,7.5),breaks=c(0.4,0.6,1,1.5,2.5,4.5,7.5),trans="log10")+
  geom_point()+geom_errorbarh(height=0.1)+geom_vline(xintercept=1,color="grey",show.legend=0)+labs(y= "",x= "Odds")+theme_classic()+
  theme(text=element_text(size=11,face="bold"))

ggsave("Bayes_lasso_hpd_fear.png",plot=forrest_fear,width=7,height=7,units= "in", dpi=300)

forrest_lab <- ggplot(lab_models2[["stanreg_models"]][["model9"]]$stan_summary %>% as.data.frame %>%rownames_to_column %>% filter(!(rowname %in% c("mean_PPD","log-posterior","(Intercept)"))&sign(`10%`)==sign(`90%`))%>%arrange(`10%`)%>%left_join(forrest_labels,by=c("rowname"= "variable"))%>% mutate(description=factor(description, levels=description)),aes(y=description,xmin=exp(`10%`),x=exp(`50%`),xmax=exp(`90%`)))+
  scale_x_continuous(limits=c(0.4,7.5),breaks=c(0.4,0.6,1,1.5,2.5,4.5,7.5),trans="log10")+
  geom_point()+geom_errorbarh(height=0.1)+geom_vline(xintercept=1,color="grey",show.legend=0)+labs(y= "",x= "Odds")+theme_classic()+
  theme(text=element_text(size=11,face="bold"))

ggsave("Bayes_lasso_hpd_lab.png",plot=forrest_lab,width=7,height=7,units= "in", dpi=300)

forrest_lab_spec <- ggplot(lab_models_spec2[["stanreg_models"]][["model8"]]$stan_summary %>% as.data.frame %>%rownames_to_column %>% filter(!(rowname %in% c("mean_PPD","log-posterior","(Intercept)"))&sign(`10%`)==sign(`90%`))%>%arrange(`10%`)%>%left_join(forrest_labels,by=c("rowname"= "variable"))%>% mutate(description=factor(description, levels=description)),aes(y=description,xmin=exp(`10%`),x=exp(`50%`),xmax=exp(`90%`)))+
  scale_x_continuous(limits=c(0.4,7.5),breaks=c(0.4,0.6,1,1.5,2.5,4.5,7.5),trans="log10")+
  geom_point()+geom_errorbarh(height=0.1)+geom_vline(xintercept=1,color="grey",show.legend=0)+labs(y= "",x= "Odds")+theme_classic()+
  theme(text=element_text(size=11,face="bold"))

ggsave("Bayes_lasso_hpd_lab_spec.png",plot=forrest_lab_spec,width=7,height=7,units= "in", dpi=300)

neutro<-ggplot(data %>% filter(!is.na(qu_sympt_ongoing)),aes(x=as.factor(qu_sympt_ongoing), y=lab_neutrohighest,color=as.factor(patchar_gender)))+
  geom_boxplot()+
  scale_x_discrete(labels=c("0"= "No", "1"= "Yes"))+
  scale_color_manual(name = "Sex",values=c("0"= "blue", "1"= "tomato"),labels=c("0"= "Men", "1"= "Women"))+
  labs(x= "Persistent symptoms", y = "Highest % neutrophils")+
  theme_classic()
ggsave("PatGender_Neutro.png",plot=neutro,width=5,height=5,units= "in", dpi=300)

neutro1<-ggplot(data %>% filter(!is.na(qu_sympt_ongoing)),aes(x=as.factor(qu_sympt_ongoing), y=lab_neutro1_number,color=as.factor(patchar_gender)))+
  scale_y_log10()+
  geom_boxplot(alpha=0.7)+
  scale_x_discrete(labels=c("0"= "No", "1"= "Yes"))+
  scale_color_manual(name = "Sex",values=c("0"= "blue", "1"= "tomato"),labels=c("0"= "Men", "1"= "Women"))+
  labs(x= "Any persistent symptom", y = "First day neutrophil count (G/L)")+
  theme_classic()+
  theme(text=element_text(size=11,face="bold"))
ggsave("PatGender_Neutro1.png",plot=neutro1,width=5,height=5,units= "in", dpi=300)

lympho<-ggplot(data %>% filter(!is.na(qu_sympt_ongoing)),aes(x=as.factor(qu_sympt_ongoing), y=lab_lympholowest,color=as.factor(patchar_gender)))+
  geom_boxplot()+
  scale_x_discrete(labels=c("0"= "No", "1"= "Yes"))+
  scale_color_manual(name = "Sex",values=c("0"= "blue", "1"= "tomato"),labels=c("0"= "Men", "1"= "Women"))+
  labs(x= "Persistent symptoms", y = "Lowest % lymphocytes")+
  theme_classic()

ggsave("PatGender_Lympho.png",plot=lympho,width=5,height=5,units= "in", dpi=300)

gs_lympho<-ggplot(data %>%
                  filter(!is.na(gender_score)&!is.na(lab_lympholowest)&!is.na(qu_sympt_ongoing))%>%
                  mutate(gs=ntile(gender_score,3)),

                  aes(color=as.factor(qu_sympt_ongoing), y=lab_lympholowest,x=as.factor(gs)))+
  geom_boxplot()+
  scale_x_discrete(labels=c("First tertile", "Second tertile","Third tertile"))+
  scale_color_manual(name = "Any persistent symptom",values=c("0"= "darkgreen", "1"= "orange"),labels=c("0"= "No", "1"= "Yes"))+
  labs(x= "Gender score", y = "Lowest % lymphocytes")+
  theme_classic()

ggsave("GenderScore_Lympho.png",plot=gs_lympho,width=5,height=5,units= "in", dpi=300)

adm1<-ggplot(data %>% filter(!is.na(qu_sympt_ongoing)),aes(x=as.factor(qu_sympt_ongoing), y=adm_delay,color=as.factor(patchar_gender)))+scale_y_log10()+
  geom_boxplot()+
  scale_x_discrete(labels=c("0"= "No", "1"= "Yes"))+
  scale_color_manual(name = "Sex",values=c("0"= "blue", "1"= "tomato"),labels=c("0"= "Men", "1"= "Women"))+
  labs(x= "Persistent symptoms", y = "Days delay in admission")+
  theme_classic()

ggsave("PatGender_Adm1.png",plot=adm1,width=5,height=5,units= "in", dpi=300)

adm2<-ggplot(
  data %>% filter(!is.na(qu_sympt_ongoing))%>%group_by(patchar_gender,qu_sympt_ongoing)%>%summarize(total=sum(adm_delay>1),
                                                                                                    per=total/n()*100),
  aes( y=per,x=as.factor(qu_sympt_ongoing),fill=as.factor(patchar_gender)))+
  geom_bar(stat="identity", position= position_dodge())+
  scale_x_discrete(labels=c("0"= "No", "1"= "Yes"))+
  scale_fill_manual(name = "Sex",values=c("0"= "blue", "1"= "tomato"),labels=c("0"= "Men", "1"= "Women"))+
  labs(x= "Any persistent symptom", y = "Patients (%) with >1 day delay in admission")+
  theme_classic()
ggsave("PatGender_Adm2.png",plot=adm2,width=5,height=5,units= "in", dpi=300)

age<-ggplot(data %>% filter(!is.na(qu_sympt_ongoing)),aes(x=as.factor(qu_sympt_ongoing), y=adm_age,color=as.factor(patchar_gender)))+
  geom_boxplot(alpha=0.7)+
  scale_x_discrete(labels=c("0"= "No", "1"= "Yes"))+
  scale_color_manual(name = "Sex",values=c("0"= "blue", "1"= "tomato"),labels=c("0"= "Men", "1"= "Women"))+
  labs(x= "Any persistent symptom", y = "Age at diagnosis of acute infection")+
  theme_classic()+
  theme(text=element_text(size=11,face="bold"))
ggsave("PatGender_Age.png",plot=age,width=5,height=5,units= "in", dpi=300)

gs_symp6<-ggplot(data %>% filter(!is.na(qu_sympt_ongoing)),aes(x=gender_score, linetype=as.factor(covid_symp___6),color=as.factor(qu_sympt_ongoing), fill=NULL))+
  stat_density(geom="line",position="identity")+
  scale_color_manual(name="Any persistent symptom", labels=c("0"= "No", "1"= "Yes"),values=c("0"= "darkgreen", "1"= "orange"))+
  scale_linetype_manual(name = "Gastrointestinal symptoms", labels=c("0"= "No", "1"= "Yes"),values=c("0"=1,"1"=2))+
  labs(x= "Gender score", y = "Density of patients")+
  guides(linetype=guide_legend(order=2),color=guide_legend(order=1))+
  theme_classic()+
  theme(text=element_text(size=11,face= "bold"))

ggsave("Gender_score_covid_6.png",plot=gs_symp6,width=5,height=5,units= "in", dpi=300)

gs_symp3<-ggplot(data %>% filter(!is.na(qu_sympt_ongoing)),aes(x=gender_score, linetype=as.factor(covid_symp___3),color=as.factor(qu_sympt_ongoing) ,fill=NULL))+
  stat_density(geom="line",position="identity")+
  scale_color_manual(name="Any persistent symptom", labels=c("0"= "No", "1"= "Yes"),values=c("0"= "darkgreen", "1"= "orange"))+
  scale_linetype_manual(name = "Cough", labels=c("0"= "No", "1"= "Yes"),values=c("0"=1,"1"=2))+
  labs(x= "Gender score", y = "Density of patients")+
  guides(linetype=guide_legend(order=2),color=guide_legend(order=1))+
  theme_classic()+
  theme(text=element_text(size=11, face= "bold"))

ggsave("Gender_score_covid_3.png",plot=gs_symp3,width=5,height=5,units= "in", dpi=300)

gs_symp2<-ggplot(data %>% filter(!is.na(qu_sympt_ongoing)),aes(x=gender_score, linetype=as.factor(covid_symp___2),color=as.factor(spec_any_long), fill=NULL))+
  stat_density(geom="line",position="identity")+
  scale_linetype_manual(name = "Dyspnea", labels=c("0"= "No", "1"= "Yes"),values=c("0"=1,"1"=2))+
  scale_color_manual(name="Specific persistent symptoms", labels=c("0"= "No", "1"= "Yes"),values=c("0"= "darkgreen", "1"= "orange"))+
  labs(x= "Gender score", y = "Density of patients")+
  guides(linetype=guide_legend(order=2),color=guide_legend(order=1))+
  theme_classic()+
  theme(text=element_text(size=11, face = "bold"))

ggsave("Gender_score_covid_2.png",plot=gs_symp2,width=5,height=5,units= "in", dpi=300)

abschluss <- c("1"= "No educational\n qualification", "2"= "Primary education", "3"= "Secondary education/\nvocational degree","4"= "University or technical\n college degree")
gs_abschluss<-ggplot(data %>% filter(!is.na(qu_sympt_ongoing)&!is.na(qu_abschluss)),aes(x=gender_score,color=as.factor(qu_sympt_ongoing), fill=NULL))+
  stat_density(geom="line",position="identity")+
  facet_grid(rows=vars(qu_abschluss),labeller=labeller(qu_abschluss=abschluss))+
  ## scale_linetype_manual(name = "Education", labels=c("1"= "No Degree", "2"= "Grade School", "3"= "Occupational Degree","4"= "Higher Degree"),values=c("1"=1,"2"=2,"3"=3,"4"=4))+
  scale_color_manual(values=c("0"= "darkgreen", "1"= "orange"),labels=c("0"= "No", "1"= "Yes"), name= "Any persistent symptom")+
  labs(x= "Gender score", y = "Density of patients")+
  theme_classic()+
  theme(text=element_text(size=11,face = "bold"),strip.text.y = element_text(size = 8))

ggsave("Gender_score_abschluss.png",plot=gs_abschluss,width=6,height=6,units= "in", dpi=300)

bar_any<- ggplot(rbind(
data %>% filter(!is.na(qu_sympt_ongoing))%>% group_by(patchar_gender,admittedtohospital) %>% summarize(per=sum(qu_sympt_ongoing)/n()*100),
data %>% filter(!is.na(qu_sympt_ongoing))%>% group_by(patchar_gender) %>% summarize(admittedtohospital=2,per=sum(qu_sympt_ongoing)/n()*100)
),aes(x=as.factor(admittedtohospital),y=per,fill=as.factor(patchar_gender)))+
  geom_bar(stat= "identity", position=position_dodge2(padding=0),alpha=0.7,color= "grey50")+
  scale_fill_manual(name = "Sex",values=c("0"= "blue", "1"= "tomato"),labels=c("0"= "Men", "1"= "Women"))+
scale_x_discrete(labels=c("0"= "Outpatient", "1"= "Hospitalized", "2"= "Overall"),limits=rev)+
  labs(x= "", y= "Patients (%) with any persistent symptom")+
  ylim(0,65)+
  theme_classic()+
  theme(text=element_text(size=11, face = "bold"))

ggsave("Any_persistent_symptoms.png",plot=bar_any,width=5,height=5,units= "in", dpi=300)

bar_spec<- ggplot(rbind(
data %>% filter(!is.na(qu_sympt_ongoing))%>% group_by(patchar_gender,admittedtohospital) %>% summarize(per=sum(spec_any_long)/n()*100),
data %>% filter(!is.na(qu_sympt_ongoing))%>% group_by(patchar_gender) %>% summarize(admittedtohospital=2,per=sum(spec_any_long)/n()*100)
),aes(x=as.factor(admittedtohospital),y=per,fill=as.factor(patchar_gender)))+
  geom_bar(stat= "identity", position=position_dodge2(padding=0),alpha=0.7,color= "grey50")+
  scale_fill_manual(name = "Sex",values=c("0"= "blue", "1"= "tomato"),labels=c("0"= "Men", "1"= "Women"))+
scale_x_discrete(labels=c("0"= "Outpatient", "1"= "Hospitalized", "2"= "Overall"),limits=rev)+
  labs(x= "", y= "Patients (%) with specific persistent symptoms")+
  ylim(0,65)+
  theme_classic()+
  theme(text=element_text(size=11, face = "bold"))

ggsave("Spec_persistent_symptoms.png",plot=bar_spec,width=5,height=5,units= "in", dpi=300)
