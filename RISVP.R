##########################
# RISVP ports
# date: 01 abr 2025
# https://otexts.com/fpp3/
# see also https://jtr13.github.io/cc19/time-series-modeling-with-arima-in-r.html
#########################

t0 <- proc.time() [3]
par(mfrow = c(1, 1))

library(dplyr)
library(forecast)
library(vars)
library(feasts)
library(fable)
library(fabletools)
library(fpp2)
library(tsibble)
library(ggplot2)
library(cluster)
library(fpc)
library(corrplot)
library(RColorBrewer)
library(ggbiplot)
library(dlm)
library(MTS)
library(opera)
library(forecastHybrid)

############## >>>>>>>>>> CS 00

############# auxiliary functions
# MAPE calculation for the last nper observations
fmape <- function(yobs, yest, nper = 3) {
  vyobs <- yobs[(length(yobs) - nper + 1) : length(yobs)]
  vyest <- yest[(length(yest) - nper + 1) : length(yest)]
  mean(abs((vyobs - vyest) / vyobs) * 100)
}

## https://robjhyndman.com/hyndsight/tscharacteristics/

# f1 maps (0,infinity) to (0,1)
f1 <- function(x, a, b) {
  eax <- exp(a * x)
  if (eax == Inf) f1eax <- 1 else f1eax <- (eax - 1) / (eax + b)
  return(f1eax)
}

# f2 maps (0,1) onto (0,1)
f2 <- function(x, a, b) {
  eax <- exp(a * x)
  ea <- exp(a)
  return((eax - 1) / (eax + b) * (ea + b) / (ea - 1))
}

# decomposition data - detrend & deseasonal
decomp <- function(x, transform = TRUE) {
  require(forecast)
  # Transform series
  if (transform & min(x, na.rm = TRUE) >= 0) {
    lambda <- BoxCox.lambda(na.contiguous(x))
    x <- BoxCox(x, lambda)
  } else {
    lambda <- NULL
    transform <- FALSE
  }
  # Seasonal data
  if (frequency(x) > 1) {
    x.stl <- stl(x, s.window = "periodic", na.action = na.contiguous)
    trend <- x.stl$time.series[, 2]
    season <- x.stl$time.series[, 1]
    remainder <- x - trend - season
  } else # Nonseasonal data
  {
    require(mgcv)
    tt <- 1:length(x)
    trend <- rep(NA, length(x))
    trend[!is.na(x)] <- fitted(gam(x ~ s(tt)))
    season <- NULL
    remainder <- x - trend
  }
  return(list(
    x = x,
    trend = trend,
    season = season,
    remainder = remainder,
    transform = transform,
    lambda = lambda
  ))
}

# === Following function computes all measures

measures <- function(x) {
  require(forecast)
  
  N <- length(x)
  freq <- findfrequency(x)
  fx <- c(frequency = (exp((freq - 1) / 50) - 1) / (1 + exp((freq - 1) / 50)))
  x <- ts(x, f = freq)
  
  # Decomposition
  decomp.x <- decomp(x)
  
  # Adjust data
  if (freq > 1) {
    fits <- decomp.x$trend + decomp.x$season
  } else {
    # Nonseasonal data
    fits <- decomp.x$trend
  }
  adj.x <- decomp.x$x - fits + mean(decomp.x$trend, na.rm = TRUE)
  
  # Backtransformation of adjusted data
  if (decomp.x$transform) {
    tadj.x <- InvBoxCox(adj.x, decomp.x$lambda)
  } else {
    tadj.x <- adj.x
  }
  
  # Trend and seasonal measures
  # avoids the divide by zero problem by testing if the variances are close to zero first
  v.adj <- var(adj.x, na.rm = TRUE)
  if (freq > 1) {
    detrend <- decomp.x$x - decomp.x$trend
    deseason <- decomp.x$x - decomp.x$season
    trend <- ifelse(
      var(deseason, na.rm = TRUE) < 1e-10,
      0,
      max(0, min(1, 1 - v.adj / var(deseason, na.rm = TRUE)))
    )
    season <- ifelse(
      var(detrend, na.rm = TRUE) < 1e-10,
      0,
      max(0, min(1, 1 - v.adj / var(detrend, na.rm = TRUE)))
    )
  } else # Nonseasonal data
  {
    trend <- ifelse(
      var(decomp.x$x, na.rm = TRUE) < 1e-10,
      0,
      max(0, min(1, 1 - v.adj / var(decomp.x$x, na.rm = TRUE)))
    )
    season <- 0
  }
  
  m <- c(fx, trend, season)
  
  # Measures on original data
  xbar <- mean(x, na.rm = TRUE)
  s <- sd(x, na.rm = TRUE)
  
  # Serial correlation
  Q <- Box.test(x, lag = 10)$statistic / (N * 10)
  fQ <- f2(Q, 7.53, 0.103)
  
  # Nonlinearity
  p <- tseries::terasvirta.test(na.contiguous(x))$statistic
  fp <- f1(p, 0.069, 2.304)
  
  # Skewness
  sk <- abs(mean((x - xbar)^3, na.rm = TRUE) / s^3)
  fs <- f1(sk, 1.510, 5.993)
  
  # Kurtosis
  k <- mean((x - xbar)^4, na.rm = TRUE) / s^4
  fk <- f1(k, 2.273, 11567)
  
  # Hurst=d+0.5 where d is fractional difference.
  H <- fracdiff::fracdiff(na.contiguous(x), 0, 0)$d + 0.5
  
  # Lyapunov Exponent
  if (freq > N - 10) stop("Insufficient data")
  Ly <- numeric(N - freq)
  for (i in 1:(N - freq)) {
    idx <- order(abs(x[i] - x))
    idx <- idx[idx < (N - freq)]
    j <- idx[2]
    Ly[i] <- log(abs((x[i + freq] - x[j + freq]) / (x[i] - x[j]))) / freq
    if (is.na(Ly[i]) | Ly[i] == Inf | Ly[i] == -Inf) Ly[i] <- NA
  }
  Lyap <- mean(Ly, na.rm = TRUE)
  fLyap <- exp(Lyap) / (1 + exp(Lyap))
  if (is.na(fLyap)) fLyap = NA  ## added 24 mar 2025
  
  m <- c(m, fQ, fp, fs, fk, H, fLyap)
  
  # Measures on adjusted data
  xbar <- mean(tadj.x, na.rm = TRUE)
  s <- sd(tadj.x, na.rm = TRUE)
  
  # Serial
  Q <- Box.test(adj.x, lag = 10)$statistic / (N * 10)
  fQ <- f2(Q, 7.53, 0.103)
  
  # Nonlinearity
  p <- tseries::terasvirta.test(na.contiguous(adj.x))$statistic
  fp <- f1(p, 0.069, 2.304)
  
  # Skewness
  sk <- abs(mean((tadj.x - xbar)^3, na.rm = TRUE) / s^3)
  fs <- f1(sk, 1.510, 5.993)
  
  # Kurtosis
  k <- mean((tadj.x - xbar)^4, na.rm = TRUE) / s^4
  fk <- f1(k, 2.273, 11567)
  
  m <- c(m, fQ, fp, fs, fk)
  names(m) <- c(
    "frequency",
    "trend",
    "seasonal",
    "autocorrelation",
    "non-linear",
    "skewness",
    "kurtosis",
    "Hurst",
    "Lyapunov",
    "dc autocorrelation",
    "dc non-linear",
    "dc skewness",
    "dc kurtosis"
  )
  
  return(m)
}

############## <<<<<<<<<<  CS 00

############## >>>>>>>>>>  CS 01
#############  box cox transformations
# https://robjhyndman.com/nyc2018/2-1-Transformations.pdf

par(mfrow=c(1,1))

plot(AirPassengers)

par(mfrow=c(2,1))

lambda <- BoxCox.lambda(AirPassengers,lower=0)
air.fit <- Arima(AirPassengers, order=c(0,1,1),
                 seasonal=list(order=c(0,1,1),period=12))
air.fit.lambda <- Arima(AirPassengers, order=c(0,1,1),
                        seasonal=list(order=c(0,1,1),period=12), lambda=lambda)
plot(forecast(air.fit))
acc1 <- accuracy(forecast(air.fit))
plot(forecast(air.fit.lambda))
acc2 <- accuracy(forecast(air.fit.lambda))

rbind(acc1, acc2)

par(mfrow=c(1,1))

## errors improved a little  using lambda

### Box.test
#  Computes the Box–Pierce or Ljung–Box test statistic for examining the null hypothesis of independence 
#   in a given time series. These are sometimes known as ‘portmanteau’ tests

air.fit <- Arima(AirPassengers, order=c(0,1,1),
                 seasonal=list(order=c(0,1,1),period=12))
Box.test(air.fit$residuals, lag = 1, type = "Box-Pierce")
Box.test(air.fit$residuals, lag = 1, type = "Ljung-Box")

## p=value > 0.05: we do not reject the hypotheses of independence at 95% level
## 

############## <<<<<<<<<<  CS 01

############## >>>>>>>>>>  CS 02
############# reading data and creating time series
library(readxl)
nRISPV <- read_excel("ships_RISPV.xlsx")
ts.data <- ts(nRISPV, start = c(2020, 1), frequency = 12)
tsb.data <- as_tsibble(ts.data) ### if needed
## plotting series
autoplot(ts.data, main = "ships in Brazilian ports")
############## <<<<<<<<<  CS 02

############## >>>>>>>>>>  CS 03

############# STL decomposition e features strength
### Rio decomposition
as_tsibble(ts.data [,1]) %>%
  model(STL(value ~ trend(window = 10))) %>%
  components() %>% autoplot + ggtitle("Rio port")
feat_R <- as_tsibble(ts.data [,1]) |>
  features(value, feat_stl)
### Itaguaí decomposition
as_tsibble(ts.data [,2]) %>%
  model(STL(value ~ trend(window = 10))) %>%
  components() %>% autoplot + ggtitle("Itaguaí port")
feat_I <- as_tsibble(ts.data [,2]) |>
  features(value, feat_stl)
### Santos decomposition
as_tsibble(ts.data [,3]) %>%
  model(STL(value ~ trend(window = 10))) %>%
  components() %>% autoplot + ggtitle("Santos port")
feat_S <- as_tsibble(ts.data [,3]) |>
  features(value, feat_stl)
### Vitória decomposition
as_tsibble(ts.data [,4]) %>%
  model(STL(value ~ trend(window = 10))) %>%
  components() %>% autoplot + ggtitle("Vitória port")
feat_V <- as_tsibble(ts.data [,4]) |>
  features(value, feat_stl)
### Paranaguá decomposition
as_tsibble(ts.data [,5]) %>%
  model(STL(value ~ trend(window = 10))) %>%
  components() %>% autoplot + ggtitle("Paranaguá port")
feat_P <- as_tsibble(ts.data [,5]) |>
  features(value, feat_stl)

############## <<<<<<<<<<  CS 03

############## >>>>>>>>>>  CS 04

mat_feat <- rbind(feat_R, feat_I, feat_S, feat_V, feat_P)
mat_feat$port <- c("Rio", "Itaguaí", "Santos", "Vitória", "Paranaguá")
mat_feat[ ,c(10,1,2)]

### other features / coeficients
mat_measures <- matrix(0,5,13)
for (i in 1:5) mat_measures[i,] <- measures(ts.data[ ,i])
row.names(mat_measures) <- c("Rio", "Itaguaí", "Santos", "Vitória", "Paranaguá")
colnames(mat_measures) <- names(measures(ts.data[ ,i]))
round(mat_measures, 3)

### more features
## time series features
tsb.data|>
  features(value, feat_stl)


############# correlation 
par(mfrow = c(1, 1))
M <-cor(ts.data[ ,1:5])
corrplot(M, method="ellipse")
Dij <- 1 - M  # correlation distance - use if necessary

############## <<<<<<<<<<  CS 04

############## >>>>>>>>>>  CS 05
###########clustering time series
df_mat_feat <- data.frame(rbind(feat_R, feat_I, feat_S, feat_V, feat_P))
row.names(df_mat_feat) <- c("Rio", "Itaguaí", "Santos", "Vitória", "Paranaguá")
Dij <- daisy(df_mat_feat, metric = "gower")   ## distance matrix
plot(hclust(Dij)) ## hierarchical complete clustering dendogram
mod.pamk <-  pamk(Dij, krange=3:3) ## based on the dendogram plot
mod.pamk$pamobject$clustering

############# time series biplot
# https://www.r-bloggers.com/2021/05/principal-component-analysis-pca-in-r/
pc <- prcomp(df_mat_feat,
             center = TRUE,
             scale. = TRUE)
attributes(pc)

g <- ggbiplot(pc,
              obs.scale = 1,
              var.scale = 1,
              groups = as.factor(mod.pamk$pamobject$clustering),
              # ellipse = TRUE,
              circle = TRUE,
              ellipse.prob = 0.68)
# g <- g + scale_color_discrete(name = '')
g <- g + theme(legend.direction = 'horizontal',
               legend.position = 'top')
print(g) +  ggtitle("PCA biplot")

############## <<<<<<<<<<   CS 05

############## >>>>>>>>>>   CS 06
############# forecasting

#### two models: rwf and meanf

nj = 1 ## Rio
fitR1 <- rwf(ts.data [1:(nrow(ts.data)-3),nj], h = 12)
fitR2 <- meanf(ts.data[1:(nrow(ts.data)-3),nj], h = 12)
accuracy(fitR1)
accuracy(fitR2)
## estimating for the last three periods
accuracy(fitR1, ts.data [(nrow(ts.data)-2):nrow(ts.data),nj])
accuracy(fitR2, ts.data [(nrow(ts.data)-2):nrow(ts.data),nj])
## plotting
#par(mfrow = c(1,1))
plot(fitR1, main = "random walk - Rio")
plot(fitR2, main = "mean - Rio")

nj = 2 ## Itaguaí
fitR1 <- rwf(ts.data [1:(nrow(ts.data)-3),nj], h = 12)
fitR2 <- meanf(ts.data[1:(nrow(ts.data)-3),nj], h = 12)
accuracy(fitR1)
accuracy(fitR2)
## estimating for the last three periods
accuracy(fitR1, ts.data [(nrow(ts.data)-2):nrow(ts.data),nj])
accuracy(fitR2, ts.data [(nrow(ts.data)-2):nrow(ts.data),nj])
## plotting
plot(fitR1, main = "random walk - Itaguaí")
plot(fitR2, main = "mean - Itaguaí")

nj = 3 ## Santos
fitR1 <- rwf(ts.data [1:(nrow(ts.data)-3),nj], h = 12)
fitR2 <- meanf(ts.data[1:(nrow(ts.data)-3),nj], h = 12)
accuracy(fitR1)
accuracy(fitR2)
## estimating for the last three periods
accuracy(fitR1, ts.data [(nrow(ts.data)-2):nrow(ts.data),nj])
accuracy(fitR2, ts.data [(nrow(ts.data)-2):nrow(ts.data),nj])
## plotting
plot(fitR1, main = "random walk - Santos")
plot(fitR2, main = "mean - Santos")

nj = 4 ## Vitória
fitR1 <- rwf(ts.data [1:(nrow(ts.data)-3),nj], h = 12)
fitR2 <- meanf(ts.data[1:(nrow(ts.data)-3),nj], h = 12)
accuracy(fitR1)
accuracy(fitR2)
## estimating for the last three periods
accuracy(fitR1, ts.data [(nrow(ts.data)-2):nrow(ts.data),nj])
accuracy(fitR2, ts.data [(nrow(ts.data)-2):nrow(ts.data),nj])
## plotting
plot(fitR1, main = "random walk - Vitória")
plot(fitR2, main = "mean - Vitória")

nj = 5 ## Paranaguá
fitR1 <- rwf(ts.data [1:(nrow(ts.data)-3),nj], h = 12)
fitR2 <- meanf(ts.data[1:(nrow(ts.data)-3),nj], h = 12)
accuracy(fitR1)
accuracy(fitR2)
## estimating for the last three periods
accuracy(fitR1, ts.data [(nrow(ts.data)-2):nrow(ts.data),nj])
accuracy(fitR2, ts.data [(nrow(ts.data)-2):nrow(ts.data),nj])
## plotting
plot(fitR1, main = "random walk - Paranaguá")
plot(fitR2, main = "mean - Paranaguá")

## Seasonal Holt-Winters

## Rio
hwR <- HoltWinters(ts.data[ ,1])
plot(hwR, main = "Holt Winters - port of Rio")
plot(fitted(hwR), main = "Holt Winters - port of Rio")
pHWR <- predict(hwR, n.ahead = 12, prediction.interval = TRUE, level = 0.95)
autoplot(pHWR, main = "Holt Winters - port of Rio")


## Itaguaí
hwI <- HoltWinters(ts.data[ ,2])
plot(hwI, main = "Holt Winters - port of Itaguaí")
plot(fitted(hwI), main = "Holt Winters - port of Itaguaí")
pHWI <- predict(hwI, n.ahead = 12, prediction.interval = TRUE, level = 0.95)
autoplot(pHWI, main = "Holt Winters - port of Itaguaí")

## Santos
hwS <- HoltWinters(ts.data[ ,3])
plot(hwS, main = "Holt Winters - port of Santos")
plot(fitted(hwS), main = "Holt Winters - port of Santos")
pHWS <- predict(hwS, n.ahead = 12, prediction.interval = TRUE, level = 0.95)
autoplot(pHWS, main = "Holt Winters - port of Santos")

## Vitória
hwV <- HoltWinters(ts.data[ ,4])
plot(hwV, main = "Holt Winters - port of Vitória")
plot(fitted(hwV), main = "Holt Winters - port of Vitória")
pHWV <- predict(hwV, n.ahead = 12, prediction.interval = TRUE, level = 0.95)
autoplot(pHWV, main = "Holt Winters - port of Vitória")

## Paranaguá
hwP <- HoltWinters(ts.data[ ,5])
plot(hwP, main = "Holt Winters - port of Paranaguá")
plot(fitted(hwP), main = "Holt Winters - port of Paranaguá")
pHWP <- predict(hwV, n.ahead = 12, prediction.interval = TRUE, level = 0.95)
autoplot(pHWP, main = "Holt Winters - port of Paranaguá")

### arima models

## Rio
fitR <- forecast(auto.arima(ts.data[ ,1]), h=12)
checkresiduals(fitR, lag=36) 
accuracy(fitR)
plot(fitR)

## Itaguaí
fitI <- forecast(auto.arima(ts.data[ ,2]), h=12)
checkresiduals(fitI, lag=36) 
accuracy(fitI)
plot(fitI)

## Santos
fitS <- forecast(auto.arima(ts.data[ ,3]), h=12)
checkresiduals(fitS, lag=36) 
accuracy(fitS)
plot(fitS)

## Vitória
fitV <- forecast(auto.arima(ts.data[ ,4]), h=12)
checkresiduals(fitV, lag=36) 
accuracy(fitV)
plot(fitV)

## Paranaguá
fitP <- forecast(auto.arima(ts.data[ ,5]), h=12)
checkresiduals(fitP, lag=36) 
accuracy(fitP)
plot(fitP)

############## <<<<<<<<<<<<   CS 06

############## >>>>>>>>>>>>   CS 07
########## exponential smoothing

########## ETS decomposition
#### ets forecasting and forecast

fitR <- ets(ts.data [ ,1])
autoplot(fitR) + ggtitle("ets decomposition - Rio port") 
autoplot(forecast(fitR, model = "ZZZ"), main = "ets decomposition - Rio port")
accuracy(forecast(fitR, model = "ZZZ"))

fitI <- ets(ts.data [ ,2])
autoplot(fitR) + ggtitle("ets decomposition - Itaguaí port") 
autoplot(forecast(fitI, model = "ZZZ"), main = "ets decomposition - Itaguaí port")
accuracy(forecast(fitI, model = "ZZZ"))

fitS <- ets(ts.data [ ,3])
autoplot(fitS) + ggtitle("ets decomposition - Santos port") 
autoplot(forecast(fitS, model = "ZZZ"), main = "ets decomposition - Santos port")
accuracy(forecast(fitS, model = "ZZZ"))

fitV <- ets(ts.data [ ,4])
autoplot(fitV) + ggtitle("ets decomposition - Vitória port") 
autoplot(forecast(fitV, model = "ZZZ"), main = "ets decomposition - Vitória port")
accuracy(forecast(fitV, model = "ZZZ"))

fitP <- ets(ts.data [ ,5])
autoplot(fitP) + ggtitle("ets decomposition - Paranaguá port") 
autoplot(forecast(fitP, model = "ZZZ"), main = "ets decomposition - Paranaguá port")
accuracy(forecast(fitP, model = "ZZZ"))

##### arima vs ets - Rio port

train <- ts(ts.data[1:48,1], start = c(2020,1), freq = 12)
test  <- ts(ts.data[49:nrow(ts.data)], start = c(2024,1), freq = 12)

### train
fitR_a_train <- forecast(auto.arima(train), h=12)
checkresiduals(fitR_a_train, lag=36) 
accuracy(fitR_a_train)
plot(fitR_a_train)


fitR_e_train <- forecast(ets(train), h=12)
checkresiduals(fitR_e_train, lag=36) 
accuracy(fitR_e_train)
plot(fitR_e_train)

### test
fitR_a_test <- forecast(auto.arima(test), h=12)
checkresiduals(fitR_a_test, lag=36) 
accuracy(fitR_a_test)
plot(fitR_a_test)


fitR_e_test <- forecast(ets(test), h=12)
checkresiduals(fitR_e_test, lag=36) 
accuracy(fitR_e_test)
plot(fitR_e_test)

# Generate forecasts and compare accuracy over the test set
r_arima  <-  fitR_a_train |> accuracy()
r_ets    <-  fitR_e_train |> accuracy()
rf_arima <-  fitR_a_test  |> accuracy()
rf_ets   <-  fitR_e_test |>  accuracy() 

df.acc <- rbind(r_arima, r_ets, rf_arima, rf_ets)
row.names(df.acc) <- c("arima_train", "ets_train", "arima_test", "eta_test")
df.acc

### arima is a little better 

## so we forecast for arima for three years
fitR_arima <- forecast(auto.arima(ts.data[ ,1]), h=36)
checkresiduals(fitR_arima, lag=36) 
accuracy(fitR_arima)
plot(fitR_arima)

############## <<<<<<<<<<<< CS 07
############## >>>>>>>>>>>>   CS 08
####### tbats decomposition and forecast

## Rio
fitR <- tbats(ts.data[ ,1])
autoplot(fitR, main = "BATS decomposition - Rio port")
FfitR <- forecast(fitR, h = 12)
autoplot(FfitR, main = "BATS decomposition - Rio port - forecast")
accuracy(forecast(FfitR))

## Itaguaí
fitI <- tbats(ts.data[ ,2])
autoplot(fitI, main = "BATS decomposition - Itaguaí port")
FfitI <- forecast(fitI, h = 12)
autoplot(FfitI, main = "BATS decomposition - Itaguaí port - forecast")
accuracy(forecast(FfitI))

## Santos
fitS <- tbats(ts.data[ ,3])
plot(fitS, main = "BATS decomposition - Santos port") ## autoplot does not work here...
FfitS <- forecast(fitS, h = 12)
autoplot(FfitS, main = "BATS decomposition - Santos port - forecast")
accuracy(forecast(FfitS))

## Vitória
fitV <- tbats(ts.data[ ,4])
autoplot(fitV, main = "BATS decomposition - Vitória port")
FfitV <- forecast(fitV, h = 12)
autoplot(FfitV, main = "BATS decomposition - Vitória port - forecast")
accuracy(forecast(FfitV))

## Paranaguá
fitP <- tbats(ts.data[ ,5])
autoplot(fitP, main = "BATS decomposition - Paranaguá port")
FfitP <- forecast(fitP, h = 12)
autoplot(FfitP, main = "BATS decomposition - Paranaguá port - forecast")
accuracy(forecast(FfitP))

############## <<<<<<<<<<<<<  CS 08
############## >>>>>>>>>>>>   CS 09
########## redes neurais NNETAR
### Rio
tsRio <- ts.data[ ,1] |> as_tsibble()
fitRio <- tsRio |>
  model(NNETAR(box_cox(value, 0.15)))
fitRio |>
  forecast(h = 30) |>
  autoplot(tsRio) +
  labs(x = "Month Year", y = "Ships", title = "Rio port")

# prediction intervals
fitRio |>
  generate(times = 9, h = 30) |>
  autoplot(.sim) +
  autolayer(tsRio, value) +
  theme(legend.position = "none") +
  ggtitle("Rio port")

## similar for the other ports
############## <<<<<<<<<<<<<  CS 09
############## >>>>>>>>>>>>   CS 10

##############  VAR models
##Brazilian ports 
head(ts.data)
zt=ts.data
m1=VAR(zt,p=2)  ### MTS package
pVAR <- VARpred(m1,12)
ts.VARpred <- ts(pVAR$pred, start = c(2026,1), frequency = 12)
autoplot(ts.VARpred, main = "Var MTS - Brazilian ports", xlab = "% of the year", ylab = "no. of ships")

##Brazilian ports - differenced
head(ts.data)
zt=diffM(ts.data)
m1=VAR(zt,p=2)
pVAR <- VARpred(m1,12)
ts.VARpred <- ts(pVAR$pred, start = c(2026,1), frequency = 12)
autoplot(ts.VARpred, main = "Var MTS - Brazilian ports - differenced", xlab = "% of the year", ylab = "no. of ships")

############## <<<<<<<<<<<< CS 10
############## >>>>>>>>>>>>   CS 11

#### decomposing time series with dlm - the case of Rio
# Rio

lRio <- log(ts.data[ ,1])
dlmRio <- dlmModPoly() + dlmModSeas(12)
buildFun <- function(x) {
  diag(W(dlmRio))[2:3] <- exp(x[1:2])
  V(dlmRio) <- exp(x[3])
  return(dlmRio)
}
(fit <- dlmMLE(lRio, parm = rep(0, 3), build = buildFun))$conv
#[1] 0
dlmRio <- buildFun(fit$par)
drop(V(dlmRio))
#[1] 0.121
diag(W(dlmRio))[2:3]
# [1]

#Based on the fitted model, we can compute the smoothing estimates of
#the states. This can be used to obtain a decomposition of the data into a
#smooth trend plus a stochastic seasonal component, subject to measurement
#error.
rioSmooth <- dlmSmooth(lRio, mod = dlmRio)
x <- cbind(lRio, dropFirst(rioSmooth$s[,c(1,3)]))
colnames(x) <- c("Rio", "Trend", "Seasonal")
plot(x, type = 'o', main = "Rio port")

# Forecasting
# Means and variances of the forecast distributions of states and observations
# can be obtained with the function dlmForecast, as illustrated in the code
# below. Means and variances of future states and observations are returned
# in a list as components a, R, f, and Q.
rioFilt <- dlmFilter(lRio, mod = dlmRio)
rioFore <- dlmForecast(rioFilt, nAhead = 20)
sqrtR <- sapply(rioFore$R, function(x) sqrt(x[1,1]))
pl <- rioFore$a[,1] + qnorm(0.05, sd = sqrtR)
pu <- rioFore$a[,1] + qnorm(0.95, sd = sqrtR)
x <- ts.union(window(lRio, start = c(2020, 1)),
              + window(rioSmooth$s[,1], start = c(2020, 1)),
              + rioFore$a[,1], pl, pu)
plot(x, plot.type = "single", type = 'o', pch = c(1, 0, 20, 3, 3),
     col = c("darkgrey", "darkgrey", "brown", "green", "green"),
     xlab = "time", ylab = "Rio port", main = "Rio port")
legend("bottomright", legend = c("Observed",
                                 "Smoothed (deseasonalized)",
                                 "Forecasted level", "90% probability limit"),
       bty = 'n', pch = c(1, 0, 20, 3, 3), lty = 1,
       col = c("darkgrey", "darkgrey", "brown", "green", "green"))
########## neural nets

############## <<<<<<<<<<<<  CS 11
############## >>>>>>>>>>>>   CS 12

### nnetar 
fitR <- nnetar(ts.data[ ,1]) ## Rio
fcast <- forecast(fitR, h=20, PI=TRUE, npaths=100)
accuracy(fcast)
autoplot(fcast) + ggtitle("nnetar - Rio port") 

fitI <- nnetar(ts.data[ ,1]) ## Itaguaí
fcast <- forecast(fitI, h=20, PI=TRUE, npaths=100)
accuracy(fcast)
autoplot(fcast) + ggtitle("nnetar - Itaguaí port") 

fitS <- nnetar(ts.data[ ,1]) ## Santos
fcast <- forecast(fitS, h=20, PI=TRUE, npaths=100)
accuracy(fcast)
autoplot(fcast) + ggtitle("nnetar - Santos port") 

fitV <- nnetar(ts.data[ ,1]) ## Vitória
fcast <- forecast(fitV, h=20, PI=TRUE, npaths=100)
accuracy(fcast)
autoplot(fcast) + ggtitle("nnetar - Vitória port") 

fitP <- nnetar(ts.data[ ,1]) ## Paranaguá
fcast <- forecast(fitP, h=20, PI=TRUE, npaths=100)
accuracy(fcast)
autoplot(fcast) + ggtitle("nnetar - Paranaguá port") 

############## <<<<<<<<<<<<  CS 12
############## >>>>>>>>>>>>   CS 13
# Bootstrapping time series

## Rio
tsb.Rio <- tsb.data |>
  filter(key == "Rio") 

# Generate bootstrapped versions of the time series using the Box-Cox and Loess-based decomposition bootstrap.

bootseries <- bld.mbb.bootstrap(ts.data[ ,1], num = 10) %>%
  as.data.frame() %>% ts(start=2020, frequency=12)
autoplot(ts.data[ ,1]) +
  autolayer(bootseries, colour=TRUE) +
  autolayer(ts.data[ ,1], colour=FALSE) +
  ylab("Bootstrapped series") + guides(colour="none") + ggtitle ("Bootstrapped series - Rio port - 10 series")

# Prediction intervals from bootstrapped series
## case of Rio port

##################### Rio port file
nsim <- 1000L
sim <- bld.mbb.bootstrap(ts.data[ ,1], nsim)

h <- 36L
future <- matrix(0, nrow=nsim, ncol=h)
for(i in seq(nsim)) future[i,] <- simulate(ets(sim[[i]]), nsim=h)

start <- tsp(ts.data[ ,1])[2]+1/12
simfc <- structure(list(
  mean = ts(colMeans(future), start=start, frequency=12),
  lower = ts(apply(future, 2, quantile, prob=0.025),
             start=start, frequency=12),
  upper = ts(apply(future, 2, quantile, prob=0.975),
             start=start, frequency=12),
  level=95),
  class="forecast")

etsfc <- forecast(ets(ts.data[ ,1]), h=h, level=95)
autoplot(ts.data[ ,1]) +
  ggtitle("Ships - Rio port") +
  xlab("MonthYear") + ylab("no. of ships") +
  autolayer(simfc, series="Simulated") +
  autolayer(etsfc, series="ETS")

# Bagged ETS forecasts
sim <- bld.mbb.bootstrap(ts.data[ ,1], 10) %>%
  as.data.frame() %>%
  ts(frequency=12, start=2020)
fc <- purrr::map(as.list(sim),
                 function(x){forecast(ets(x))[["mean"]]}) %>%
  as.data.frame() %>%
  ts(frequency=12, start=start)
autoplot(ts.data[ ,1]) +
  autolayer(sim, colour=TRUE) +
  autolayer(fc, colour=TRUE) +
  autolayer(ts.data[ ,1], colour=FALSE) +
  ylab("Bootstrapped series") +
  guides(colour="none")

etsfc <- ts.data[ ,1] %>% ets() %>% forecast(h=36)
baggedfc <- ts.data[ ,1] %>% baggedETS() %>% forecast(h=36)
autoplot(ts.data[ ,1]) +
  autolayer(baggedfc, series="BaggedETS", PI=FALSE) +
  autolayer(etsfc, series="ETS", PI=FALSE) +
  guides(colour=guide_legend(title="Forecasts")) + 
  ggtitle ("Rio bagged forecasts")

############## <<<<<<<<<<<<  CS 13
############## >>>>>>>>>>>>   CS 14
############ combining forecasts
train <- ts(ts.data[1:48,1], start = c(2020,1), freq = 12)
test  <- ts(ts.data[49:nrow(ts.data)], start = c(2024,1), freq = 12)


### train
fitR_a_train <- forecast(auto.arima(train), h=12)
checkresiduals(fitR_a_train, lag=36) 
accuracy(fitR_a_train)
plot(fitR_a_train)


fitR_e_train <- forecast(ets(train), h=12)
checkresiduals(fitR_e_train, lag=36) 
accuracy(fitR_e_train)
plot(fitR_e_train)

### test
fitR_a_test <- forecast(auto.arima(test), h=12)
checkresiduals(fitR_a_test, lag=36) 
accuracy(fitR_a_test)
plot(fitR_a_test)


fitR_e_test <- forecast(ets(test), h=12)
checkresiduals(fitR_e_test, lag=36) 
accuracy(fitR_e_test)
plot(fitR_e_test)

# Generate forecasts and compare accuracy over the test set
r_arima  <-  fitR_a_train |> accuracy()
r_ets    <-  fitR_e_train |> accuracy()
rf_arima <-  fitR_a_test  |> accuracy()
rf_ets   <-  fitR_e_test |>  accuracy() 

df.acc <- rbind(r_arima, r_ets, rf_arima, rf_ets)
row.names(df.acc) <- c("arima_train", "ets_train", "arima_test", "eta_test")
df.acc

## so we forecast for arima for three years
fitR_arima <- forecast(auto.arima(ts.data[ ,1]), h=36)
checkresiduals(fitR_arima, lag=36) 
accuracy(fitR_arima)
plot(fitR_arima)


######### combining forecasts
# for Santos port

train <- window(ts.data[ ,3], end=c(2023,12))
test  <- window(ts.data[ ,3], start=c(2024,1))

## forecastHybrid
library(forecastHybrid)
fit1 <- hybridModel(train, weights="equal")
fit2 <- hybridModel(train, weights="insample")
fc1 <- forecast(fit1, h=h)
fc2 <- forecast(fit2, h=h)
autoplot(fc1) + ggtitle("Combining forecasts-  port of Santos - Hybrid 1") + xlab("Year") +
  ylab(expression("no. ships"))
autoplot(fc2) + ggtitle("Combining forecasts-  port of Santos - Hybrid 2") + xlab("Year") +
  ylab(expression("no. ships"))

############## <<<<<<<<<  CS 14


( time.minutes <- (proc.time()[3] - t0) /60 )
o

