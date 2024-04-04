
# Data setting and generating

set.seed(2022021323)

num_train <- 50000
num_test <- 5000
true_beta1 <- c(1,rep(1,3))
true_beta2 <- c(1,rep(1,3),rep(0,47))

generated.uncorrelated <- function(p){
  true_beta <- c(1,rep(1,3),rep(0,p-3))
  x <- matrix(rnorm((num_train+num_test)*p),num_train+num_test,p)
  mu <- exp(1+x%*%true_beta[-1])
  y <- rpois(length(mu), mu)
  x_train <- x[1:num_train,]
  x_test <- x[-(1:num_train),]
  y_train <- y[1:num_train]
  y_test <- y[-(1:num_train)]
  return(list(x_train = x_train, x_test = x_test, y_train = y_train, y_test = y_test))
}

generated.correlated <- function(p,rho){
  true_beta <- c(1,rep(1,3),rep(0,p-3))
  x <- matrix(rnorm((num_train+num_test)*p),num_train+num_test,p)
  sigma <- matrix(0, nrow = p, ncol = p)
  for (i in 1:p) {
    for (j in 1:p) {
      sigma[i, j] <- rho ^ abs(i - j)
    }
  }
  x <- x %*% chol(sigma)
  mu <- exp(1+x%*%true_beta[-1])
  y <- rpois(length(mu), mu)
  x_train <- x[1:num_train,]
  x_test <- x[-(1:num_train),]
  y_train <- y[1:num_train]
  y_test <- y[-(1:num_train)]
  return(list(x_train = x_train, x_test = x_test, y_train = y_train, y_test = y_test))
}

set.seed(2022021323)
data1 <- generated.uncorrelated(p=3)
set.seed(2022021323)
data2 <- generated.correlated(p=3,rho=0.7)
set.seed(2022021323)
data3 <- generated.uncorrelated(p=50)
set.seed(2022021323)
data4 <- generated.correlated(p=50,rho=0.7)
X1_train <- data1$x_train ; X1_test <- data1$x_test ; y1_train <- data1$y_train ; y1_test <- data1$y_test
X2_train <- data2$x_train ; X2_test <- data2$x_test ; y2_train <- data2$y_train ; y2_test <- data2$y_test
X3_train <- data3$x_train ; X3_test <- data3$x_test ; y3_train <- data3$y_train ; y3_test <- data3$y_test
X4_train <- data4$x_train ; X4_test <- data4$x_test ; y4_train <- data4$y_train ; y4_test <- data4$y_test

# Functions_penalty

S <- function(z, lambda){
  (z - lambda) * (z > lambda) + (z + lambda) * (z < -lambda) 
}
cd.elastic <- function(x, y, lambda, alpha) {
  n <- nrow(x) ; p <- ncol(x)
  ## column-wise scaling of design matrix ##
  s <- apply(x, 2, function(x) sum(x^2)/n)
  z <- x
  # centering of y
  u <- y
  # initialization
  beta <- coef(lm(u~z-1))
  r <- u - z %*% beta
  for (iter in 1:1000) {
    new.beta <- beta
    for (j in 1:p) {
      temp <- s[j] * beta[j] + crossprod(z[,j], r)/n
      new.beta[j] <- S(temp, alpha*lambda)/(s[j]+(1-alpha)*lambda)
      r <- r - (new.beta[j] - beta[j]) * z[,j]
    }
    delta <- max(abs(new.beta - beta))
    if (delta < 1.0e-6) break
    beta <- new.beta
  }
  beta1 <- new.beta
  return(beta1)
}

cd.scad <- function(x, y, lambda, alpha=NULL, init=NULL, max.iter=100){
  n <- nrow(x); p <- ncol(x)
  s <- apply(x, 2, function(x) 1/sum(x^2))
  if(is.null(alpha)) {
    a <- 3.7/2*(1 + n*max(s))
  } else {
    a <- alpha*(1 + n*max(s))
  }
  z <- x
  u <- y
  if(is.null(init)) init <- coef(lm(u~z-1))
  beta <- init
  r <- u - z %*% beta
  for (iter in 1:100){
    new.beta <- beta
    for (j in 1:p) {
      temp <- beta[j] + crossprod(z[,j], r)*s[j]
      if(abs(temp) <= n*lambda*s[j]){
        new.beta[j] <- 0
      }else if(abs(temp) <= (1 + n*s[j])*lambda){
        if(iter <= 30){
          new.beta[j] <- temp - sign(temp)*n*lambda*s[j]
        }else{
          new.beta[j] <- beta[j] - 0.01/iter*(temp - sign(temp)*n*lambda*s[j] - beta[j])
        }
      }else if(abs(temp) < a*lambda){
        if(iter <= 30){
          new.beta[j] <- ((a-1)*temp - sign(temp)*n*a*lambda*s[j]) / (a - 1 - n*s[j])
        }else{
          new.beta[j] <- beta[j] - 0.01/iter*(((a-1)*temp - sign(temp)*n*a*lambda*s[j]) / (a - 1 - n*s[j]) - beta[j])
        }
      }else{
        if(iter <= 30){
          new.beta[j] <- temp
        }else{
          new.beta[j] <- beta[j] - 0.01/iter*(temp - beta[j])
        }
      }
      r <- r - (new.beta[j] - beta[j]) * z[,j]
    }
    delta <- max(abs(new.beta - beta))
    if (delta < 1.0e-6) break
    beta <- new.beta
  }
  beta <- new.beta
  if(iter == max.iter) warning("Algorithm mat not be converged!-2")
  c(beta)
}

# Functions_GLM

poi <- function(X, y, init=NULL, max.iter = 100, eps = 1.0e-5,lambda = NULL, alpha = NULL) {
  # scaling -- otherwise exp(eta) gets too big
  sd_y <- sd(y)
  sd_X <- apply(X, 2, sd)
  y_scale <- y/sd_y
  X_scale <- t(t(X)/sd_X)
  X <- cbind(1, X_scale)
  
  # NR
  p <- ncol(X)
  if (is.null(init)) init <- rep(0, p)
  beta <- init
  
  for (iter in 1:max.iter) {
    eta <- X %*% beta
    mu <- exp(eta)
    w <- diag(c(mu)) # mean=var for Poisson
    z <- eta + (y_scale - mu)/mu
    
    tilde_X <- sqrt(w) %*% X
    tilde_y <- sqrt(w) %*% z
    
    QR <- qr(tilde_X)
    Q <- qr.Q(QR)
    R <- qr.R(QR)
    newy <- t(Q) %*% tilde_y
    newbeta <- backsolve(R, newy)
    
    if (max(abs(newbeta - beta)) < eps) break
    beta <- newbeta
  }
  if (iter == max.iter) warning("Algorithm may not be converged!")
  
  # recovering correct beta estimate
  beta <- c(beta) * c(1, 1/sd_X) + c(log(sd_y), rep(0, p-1))
  beta
}

poi_elastic <- function(X, y, max.iter=100, eps=1.0e-5, lambda, alpha = NULL,init = NULL){
  n <- nrow(X) ; p <- ncol(X)
  ## column-wise scaling of design matrix ##
  beta <- poi(X=X,y=y)
  X <- cbind(1,X)
  for(iter in 1:max.iter){
    eta <- X %*% beta
    mu <- exp(eta) 
    w <- diag(c(mu))
    z <- eta + (y-mu)/mu
    tilde_X <- sqrt(w) %*% X
    tilde_y <- sqrt(w) %*% z
    new.beta <- cd.elastic(x=tilde_X, y=tilde_y, lambda=lambda,alpha=alpha)
    temp_resi_1 <- tilde_y - tilde_X[,-1] %*% new.beta[-1]
    temp_resi_2 <- lm(tilde_X[,1] ~ 0 +tilde_X[,-1])$residuals
    new.beta[1] <- lm(temp_resi_1 ~ 0 + temp_resi_2)$coefficients
    if( max( abs( new.beta-beta )) < eps) break
    beta <- new.beta
  }
  if(iter == max.iter) warning("Algorithm mat not be converged!")
  beta
}

poi_scad <- function(X, y, max.iter=100, eps=1.0e-5, lambda, alpha = NULL,init = NULL){
  n <- nrow(X) ; p <- ncol(X)
  ## column-wise scaling of design matrix ##
  beta <- poi(X=X,y=y)
  X <- cbind(1,X)
  for(iter in 1:max.iter){
    eta <- X %*% beta
    mu <- exp(eta) 
    w <- diag(c(mu))
    z <- eta + (y-mu)/mu
    tilde_X <- sqrt(w) %*% X
    tilde_y <- sqrt(w) %*% z
    new.beta <- cd.scad(x=tilde_X, y=tilde_y, lambda=lambda)
    temp_resi_1 <- tilde_y - tilde_X[,-1] %*% new.beta[-1]
    temp_resi_2 <- lm(tilde_X[,1] ~ 0 +tilde_X[,-1])$residuals
    new.beta[1] <- lm(temp_resi_1 ~ 0 + temp_resi_2)$coefficients
    if( max( abs( new.beta-beta )) < eps) break
    beta <- new.beta
  }
  if(iter == max.iter) warning("Algorithm mat not be converged!")
  beta
}

# Function_Simulation

find_lambda <- function(regression_func, alpha = 1, max_lambda = 5e-3, length =10 , data){
  lambdas <- seq(0, max_lambda, length=length)
  mse <- rep(0, length(lambdas))
  if(data == "1"){
    X_train <- X1_train
    y_train <- y1_train
    X_test <- X1_test
    y_test <- y1_test
  }else if(data == "2"){
    X_train <- X2_train
    y_train <- y2_train
    X_test <- X2_test
    y_test <- y2_test
  }else if(data == "3"){
    X_train <- X3_train
    y_train <- y3_train
    X_test <- X3_test
    y_test <- y3_test
  }else if(data == "4"){
    X_train <- X4_train
    y_train <- y4_train
    X_test <- X4_test
    y_test <- y4_test
  }
  best_lambda <- rep(0,5)
  for(j in 1:5){
    for(i in 1:length(lambdas)){
      if(i == 1){
        beta <- regression_func(X_train[(500*j-499):(500*j),], y_train[(500*j-499):(500*j)], lambda=lambdas[i], alpha=alpha)
      }else{
        beta <- regression_func(X_train[(500*j-499):(500*j),], y_train[(500*j-499):(500*j)], lambda=lambdas[i], alpha=alpha, init=beta)
      }
      y_pred <- exp(cbind(1, X_test) %*% beta)
      mse[i] <- mean((y_pred - y_test)^2)
    }
    best_lambda_index <- which.min(mse) 
    best_lambda[j] <- lambdas[best_lambda_index] 
  }
  return(mean(best_lambda))
}

simulation <- function(regression_func, data, p, lambda=NULL, alpha = NULL){
  true_beta <- c(1,rep(1,3),rep(0,p-3))
  result_beta <- matrix(0,100,p+1)
  CS <- rep(0, 100)
  time <- rep(0,100)
  if(data == "1"){
    X <- X1_train
    y <- y1_train
  }else if(data == "2"){
    X <- X2_train
    y <- y2_train
  }else if(data == "3"){
    X <- X3_train
    y <- y3_train
  }else if(data == "4"){
    X <- X4_train
    y <- y4_train
  }
  for(i in 1:100){
    X_sample <- X[(500*i-499):(500*i),]
    y_sample <- y[(500*i-499):(500*i)]
    start <- Sys.time()
    result_beta[i,] <- regression_func(X=X_sample,y=y_sample,lambda= lambda, alpha=alpha)
    time[i] <- Sys.time() - start
    CS[i] <- sum((result_beta[i,][-1] != 0) == (true_beta[-1] != 0))
  }
  AC <- rep(0, 100)
  AC[CS == p] <- 1
  CS_mu <- mean(CS)
  IS_mu <- p - CS_mu
  CS_sd <- IS_sd <- sd(CS)
  AC_mu <- mean(AC)
  AC_sd <- sd(AC)
  time_mu <- mean(time)
  time_sd <- sd(time)
  mse_mu <- mean((result_beta-true_beta)^2)
  beta_var <- mean(apply(sweep(result_beta, 2, apply(result_beta, 2, mean))^2,1,sum))
  bias <- sum(abs(apply(result_beta, 2, mean) - true_beta))
  obj <- list(AC_mu=AC_mu, AC_sd=AC_sd, CS_mu=CS_mu, CS_sd=CS_sd, IS_mu=IS_mu, IS_sd=IS_sd, time_mu=time_mu, time_sd=time_sd, mse_mu = mse_mu, beta_var=beta_var, bias=bias )
}

# Simulation

result_11 <- simulation(regression_func = poi, data="1",p=3)
result_12 <- simulation(regression_func = poi, data="2",p=3)
result_13 <- simulation(regression_func = poi, data="3",p=50)
result_14 <- simulation(regression_func = poi, data="4",p=50)

AC_mu_11 = result_11$AC_mu ; AC_sd_11 = result_11$AC_sd ; CS_mu_11=result_11$CS_mu ; CS_sd_11=result_11$CS_sd ; IS_mu_11=result_11$IS_mu ; IS_sd_11=result_11$IS_sd
time_mu_11 = result_11$time_mu ; time_sd_11 = result_11$time_sd ; mse_mu_11 = result_11$mse_mu ; beta_var_11 = result_11$beta_var ; bias_11 = result_11$bias

AC_mu_12 = result_12$AC_mu ; AC_sd_12 = result_12$AC_sd ; CS_mu_12=result_12$CS_mu ; CS_sd_12=result_12$CS_sd ; IS_mu_12=result_12$IS_mu ; IS_sd_12=result_12$IS_sd
time_mu_12 = result_12$time_mu ; time_sd_12 = result_12$time_sd ; mse_mu_12 = result_12$mse_mu ; beta_var_12 = result_12$beta_var ; bias_12 = result_12$bias

AC_mu_13 = result_13$AC_mu ; AC_sd_13 = result_13$AC_sd ; CS_mu_13=result_13$CS_mu ; CS_sd_13=result_13$CS_sd ; IS_mu_13=result_13$IS_mu ; IS_sd_13=result_13$IS_sd
time_mu_13 = result_13$time_mu ; time_sd_13 = result_13$time_sd ; mse_mu_13 = result_13$mse_mu ; beta_var_13 = result_13$beta_var ; bias_13 = result_13$bias

AC_mu_14 = result_14$AC_mu ; AC_sd_14 = result_14$AC_sd ; CS_mu_14=result_14$CS_mu ; CS_sd_14=result_14$CS_sd ; IS_mu_14=result_14$IS_mu ; IS_sd_14=result_14$IS_sd
time_mu_14 = result_14$time_mu ; time_sd_14 = result_14$time_sd ; mse_mu_14 = result_14$mse_mu ; beta_var_14 = result_14$beta_var ; bias_14 = result_14$bias

best_lambda_21 <- find_lambda(regression_func = poi_elastic, data = "1",length = 10, max_lambda = 0.1, alpha = 0)
best_lambda_22 <- find_lambda(regression_func = poi_elastic, data = "2",length = 10, max_lambda = 0.1, alpha = 0)
best_lambda_23 <- find_lambda(regression_func = poi_elastic, data = "3",length = 10, max_lambda = 0.1, alpha = 0)
best_lambda_24 <- find_lambda(regression_func = poi_elastic, data = "4",length = 10, max_lambda = 0.1, alpha = 0)

result_21 <- simulation(regression_func = poi_elastic, data="1",p=3, lambda = best_lambda_21, alpha = 0)
result_22 <- simulation(regression_func = poi_elastic, data="2",p=3, lambda = best_lambda_22, alpha = 0)
result_23 <- simulation(regression_func = poi_elastic, data="3",p=50, lambda = best_lambda_23, alpha = 0)
result_24 <- simulation(regression_func = poi_elastic, data="4",p=50, lambda = best_lambda_24, alpha = 0)

AC_mu_21 = result_21$AC_mu ; AC_sd_21 = result_21$AC_sd ; CS_mu_21=result_21$CS_mu ; CS_sd_21=result_21$CS_sd ; IS_mu_21=result_21$IS_mu ; IS_sd_21=result_21$IS_sd
time_mu_21 = result_21$time_mu ; time_sd_21 = result_21$time_sd ; mse_mu_21 = result_21$mse_mu ; beta_var_21 = result_21$beta_var ; bias_21 = result_21$bias

AC_mu_22 = result_22$AC_mu ; AC_sd_22 = result_22$AC_sd ; CS_mu_22=result_22$CS_mu ; CS_sd_22=result_22$CS_sd ; IS_mu_22=result_22$IS_mu ; IS_sd_22=result_22$IS_sd
time_mu_22 = result_22$time_mu ; time_sd_22 = result_22$time_sd ; mse_mu_22 = result_22$mse_mu ; beta_var_22 = result_22$beta_var ; bias_22 = result_22$bias

AC_mu_23 = result_23$AC_mu ; AC_sd_23 = result_23$AC_sd ; CS_mu_23=result_23$CS_mu ; CS_sd_23=result_23$CS_sd ; IS_mu_23=result_23$IS_mu ; IS_sd_23=result_23$IS_sd
time_mu_23 = result_23$time_mu ; time_sd_23 = result_23$time_sd ; mse_mu_23 = result_23$mse_mu ; beta_var_23 = result_23$beta_var ; bias_23 = result_23$bias

AC_mu_24 = result_24$AC_mu ; AC_sd_24 = result_24$AC_sd ; CS_mu_24=result_24$CS_mu ; CS_sd_24=result_24$CS_sd ; IS_mu_24=result_24$IS_mu ; IS_sd_24=result_24$IS_sd
time_mu_24 = result_24$time_mu ; time_sd_24 = result_24$time_sd ; mse_mu_24 = result_24$mse_mu ; beta_var_24 = result_24$beta_var ; bias_24 = result_24$bias

best_lambda_31 <- find_lambda(regression_func = poi_elastic, data = "1",length = 10, max_lambda = 0.1, alpha = 1)
best_lambda_32 <- find_lambda(regression_func = poi_elastic, data = "2",length = 10, max_lambda = 0.1, alpha = 1)
best_lambda_33 <- find_lambda(regression_func = poi_elastic, data = "3",length = 10, max_lambda = 0.5, alpha = 1)
best_lambda_34 <- find_lambda(regression_func = poi_elastic, data = "4",length = 10, max_lambda = 0.5, alpha = 1)

result_31 <- simulation(regression_func = poi_elastic, data="1",p=3, lambda = best_lambda_31, alpha = 1)
result_32 <- simulation(regression_func = poi_elastic, data="2",p=3, lambda = best_lambda_32, alpha = 1)
result_33 <- simulation(regression_func = poi_elastic, data="3",p=50, lambda = best_lambda_33, alpha = 1)
result_34 <- simulation(regression_func = poi_elastic, data="4",p=50, lambda = best_lambda_34, alpha = 1)

AC_mu_31 = result_31$AC_mu ; AC_sd_31 = result_31$AC_sd ; CS_mu_31=result_31$CS_mu ; CS_sd_31=result_31$CS_sd ; IS_mu_31=result_31$IS_mu ; IS_sd_31=result_31$IS_sd
time_mu_31 = result_31$time_mu ; time_sd_31 = result_31$time_sd ; mse_mu_31 = result_31$mse_mu ; beta_var_31 = result_31$beta_var ; bias_31 = result_31$bias

AC_mu_32 = result_32$AC_mu ; AC_sd_32 = result_32$AC_sd ; CS_mu_32=result_32$CS_mu ; CS_sd_32=result_32$CS_sd ; IS_mu_32=result_32$IS_mu ; IS_sd_32=result_32$IS_sd
time_mu_32 = result_32$time_mu ; time_sd_32 = result_32$time_sd ; mse_mu_32 = result_32$mse_mu ; beta_var_32 = result_32$beta_var ; bias_32 = result_32$bias

AC_mu_33 = result_33$AC_mu ; AC_sd_33 = result_33$AC_sd ; CS_mu_33=result_33$CS_mu ; CS_sd_33=result_33$CS_sd ; IS_mu_33=result_33$IS_mu ; IS_sd_33=result_33$IS_sd
time_mu_33 = result_33$time_mu ; time_sd_33 = result_33$time_sd ; mse_mu_33 = result_33$mse_mu ; beta_var_33 = result_33$beta_var ; bias_33 = result_33$bias

AC_mu_34 = result_34$AC_mu ; AC_sd_34 = result_34$AC_sd ; CS_mu_34=result_34$CS_mu ; CS_sd_34=result_34$CS_sd ; IS_mu_34=result_34$IS_mu ; IS_sd_34=result_34$IS_sd
time_mu_34 = result_34$time_mu ; time_sd_34 = result_34$time_sd ; mse_mu_34 = result_34$mse_mu ; beta_var_34 = result_34$beta_var ; bias_34 = result_34$bias

best_lambda_41 <- find_lambda(regression_func = poi_elastic, data = "1",length = 10, max_lambda = 0.1, alpha = 0.5)
best_lambda_42 <- find_lambda(regression_func = poi_elastic, data = "2",length = 10, max_lambda = 0.1, alpha = 0.5)
best_lambda_43 <- find_lambda(regression_func = poi_elastic, data = "3",length = 10, max_lambda = 0.4, alpha = 0.5)
best_lambda_44 <- find_lambda(regression_func = poi_elastic, data = "4",length = 10, max_lambda = 0.4, alpha = 0.5)

result_41 <- simulation(regression_func = poi_elastic, data="1",p=3, lambda = best_lambda_41, alpha = 0.5)
result_42 <- simulation(regression_func = poi_elastic, data="2",p=3, lambda = best_lambda_42, alpha = 0.5)
result_43 <- simulation(regression_func = poi_elastic, data="3",p=50, lambda = best_lambda_43, alpha = 0.5)
result_44 <- simulation(regression_func = poi_elastic, data="4",p=50, lambda = best_lambda_44, alpha = 0.5)

AC_mu_41 = result_41$AC_mu ; AC_sd_41 = result_41$AC_sd ; CS_mu_41=result_41$CS_mu ; CS_sd_41=result_41$CS_sd ; IS_mu_41=result_41$IS_mu ; IS_sd_41=result_41$IS_sd
time_mu_41 = result_41$time_mu ; time_sd_41 = result_41$time_sd ; mse_mu_41 = result_41$mse_mu ; beta_var_41 = result_41$beta_var ; bias_41 = result_41$bias

AC_mu_42 = result_42$AC_mu ; AC_sd_42 = result_42$AC_sd ; CS_mu_42=result_42$CS_mu ; CS_sd_42=result_42$CS_sd ; IS_mu_42=result_42$IS_mu ; IS_sd_42=result_42$IS_sd
time_mu_42 = result_42$time_mu ; time_sd_42 = result_42$time_sd ; mse_mu_42 = result_42$mse_mu ; beta_var_42 = result_42$beta_var ; bias_42 = result_42$bias

AC_mu_43 = result_43$AC_mu ; AC_sd_43 = result_43$AC_sd ; CS_mu_43=result_43$CS_mu ; CS_sd_43=result_43$CS_sd ; IS_mu_43=result_43$IS_mu ; IS_sd_43=result_43$IS_sd
time_mu_43 = result_43$time_mu ; time_sd_43 = result_43$time_sd ; mse_mu_43 = result_43$mse_mu ; beta_var_43 = result_43$beta_var ; bias_43 = result_43$bias

AC_mu_44 = result_44$AC_mu ; AC_sd_44 = result_44$AC_sd ; CS_mu_44=result_44$CS_mu ; CS_sd_44=result_44$CS_sd ; IS_mu_44=result_44$IS_mu ; IS_sd_44=result_44$IS_sd
time_mu_44 = result_44$time_mu ; time_sd_44 = result_44$time_sd ; mse_mu_44 = result_44$mse_mu ; beta_var_44 = result_44$beta_var ; bias_44 = result_44$bias

best_lambda_51 <- find_lambda(regression_func = poi_scad, data = "1",length = 10, max_lambda = 0.01, alpha = 1)
best_lambda_52 <- find_lambda(regression_func = poi_scad, data = "2",length = 10, max_lambda = 0.01, alpha = 1)
best_lambda_53 <- find_lambda(regression_func = poi_scad, data = "3",length = 10, max_lambda = 0.6, alpha = 1)
best_lambda_54 <- find_lambda(regression_func = poi_scad, data = "4",length = 10, max_lambda = 0.6, alpha = 1)

result_51 <- simulation(regression_func = poi_elastic, data="1",p=3, lambda = best_lambda_51, alpha = 1)
result_52 <- simulation(regression_func = poi_elastic, data="2",p=3, lambda = best_lambda_52, alpha = 1)
result_53 <- simulation(regression_func = poi_elastic, data="3",p=50, lambda = best_lambda_53, alpha = 1)
result_54 <- simulation(regression_func = poi_elastic, data="4",p=50, lambda = best_lambda_54, alpha = 1)

AC_mu_51 = result_51$AC_mu ; AC_sd_51 = result_51$AC_sd ; CS_mu_51=result_51$CS_mu ; CS_sd_51=result_51$CS_sd ; IS_mu_51=result_51$IS_mu ; IS_sd_51=result_51$IS_sd
time_mu_51 = result_51$time_mu ; time_sd_51 = result_51$time_sd ; mse_mu_51 = result_51$mse_mu ; beta_var_51 = result_51$beta_var ; bias_51 = result_51$bias

AC_mu_52 = result_52$AC_mu ; AC_sd_52 = result_52$AC_sd ; CS_mu_52=result_52$CS_mu ; CS_sd_52=result_52$CS_sd ; IS_mu_52=result_52$IS_mu ; IS_sd_52=result_52$IS_sd
time_mu_52 = result_52$time_mu ; time_sd_52 = result_52$time_sd ; mse_mu_52 = result_52$mse_mu ; beta_var_52 = result_52$beta_var ; bias_52 = result_52$bias

AC_mu_53 = result_53$AC_mu ; AC_sd_53 = result_53$AC_sd ; CS_mu_53=result_53$CS_mu ; CS_sd_53=result_53$CS_sd ; IS_mu_53=result_53$IS_mu ; IS_sd_53=result_53$IS_sd
time_mu_53 = result_53$time_mu ; time_sd_53 = result_53$time_sd ; mse_mu_53 = result_53$mse_mu ; beta_var_53 = result_53$beta_var ; bias_53 = result_53$bias

AC_mu_54 = result_54$AC_mu ; AC_sd_54 = result_54$AC_sd ; CS_mu_54=result_54$CS_mu ; CS_sd_54=result_54$CS_sd ; IS_mu_54=result_54$IS_mu ; IS_sd_54=result_54$IS_sd
time_mu_54 = result_54$time_mu ; time_sd_54 = result_54$time_sd ; mse_mu_54 = result_54$mse_mu ; beta_var_54 = result_54$beta_var ; bias_54 = result_54$bias

df <- t(data.frame(
  mse_1 = round(c(mse_mu_11, mse_mu_21, mse_mu_31, mse_mu_41, mse_mu_51), 4),
  mse_2 = round(c(mse_mu_12, mse_mu_22, mse_mu_32, mse_mu_42, mse_mu_52), 4),
  mse_3 = round(c(mse_mu_13, mse_mu_23, mse_mu_33, mse_mu_43, mse_mu_53), 4),
  mse_4 = round(c(mse_mu_14, mse_mu_24, mse_mu_34, mse_mu_44, mse_mu_54), 4),
  beta_1 = round(c(beta_var_11, beta_var_21, beta_var_31, beta_var_41, beta_var_51), 4),
  beta_2 = round(c(beta_var_12, beta_var_22, beta_var_32, beta_var_42, beta_var_52), 4),
  beta_3 = round(c(beta_var_13, beta_var_23, beta_var_33, beta_var_43, beta_var_53), 4),
  beta_4 = round(c(beta_var_14, beta_var_24, beta_var_34, beta_var_44, beta_var_54), 4),
  bias_1 = round(c(bias_11, bias_21, bias_31, bias_41, bias_51), 4),
  bias_2 = round(c(bias_12, bias_22, bias_32, bias_42, bias_52), 4),
  bias_3 = round(c(bias_13, bias_23, bias_33, bias_43, bias_53), 4),
  bias_4 = round(c(bias_14, bias_24, bias_34, bias_44, bias_54), 4),
  CS_mu_1 = c(CS_mu_11, CS_mu_21, CS_mu_31, CS_mu_41, CS_mu_51),
  CS_sd_1 = c(CS_sd_11, CS_sd_21, CS_sd_31, CS_sd_41, CS_sd_51),
  CS_mu_2 = c(CS_mu_12, CS_mu_22, CS_mu_32, CS_mu_42, CS_mu_52),
  CS_sd_2 = c(CS_sd_12, CS_sd_22, CS_sd_32, CS_sd_42, CS_sd_52),
  CS_mu_3 = c(CS_mu_13, CS_mu_23, CS_mu_33, CS_mu_43, CS_mu_53),
  CS_sd_3 = round(c(CS_sd_13, CS_sd_23, CS_sd_33, CS_sd_43, CS_sd_53), 2),
  CS_mu_4 = c(CS_mu_14, CS_mu_24, CS_mu_34, CS_mu_44, CS_mu_54),
  CS_sd_4 = round(c(CS_sd_14, CS_sd_24, CS_sd_34, CS_sd_44, CS_sd_54), 2),
  IS_mu_1 = c(IS_mu_11, IS_mu_21, IS_mu_31, IS_mu_41, IS_mu_51),
  IS_sd_1 = c(IS_sd_11, IS_sd_21, IS_sd_31, IS_sd_41, IS_sd_51),
  IS_mu_2 = c(IS_mu_12, IS_mu_22, IS_mu_32, IS_mu_42, IS_mu_52),
  IS_sd_2 = c(IS_sd_12, IS_sd_22, IS_sd_32, IS_sd_42, IS_sd_52),
  IS_mu_3 = c(IS_mu_13, IS_mu_23, IS_mu_33, IS_mu_43, IS_mu_53),
  IS_sd_3 = round(c(IS_sd_13, IS_sd_23, IS_sd_33, IS_sd_43, IS_sd_53), 2),
  IS_mu_4 = c(IS_mu_14, IS_mu_24, IS_mu_34, IS_mu_44, IS_mu_54),
  IS_sd_4 = round(c(IS_sd_14, IS_sd_24, IS_sd_34, IS_sd_44, IS_sd_54), 2),
  AC_mu_1 = c(AC_mu_11, AC_mu_21, AC_mu_31, AC_mu_41, AC_mu_51),
  AC_sd_1 = c(AC_sd_11, AC_sd_21, AC_sd_31, AC_sd_41, AC_sd_51),
  AC_mu_2 = c(AC_mu_12, AC_mu_22, AC_mu_32, AC_mu_42, AC_mu_52),
  AC_sd_2 = c(AC_sd_12, AC_sd_22, AC_sd_32, AC_sd_42, AC_sd_52),
  AC_mu_3 = c(AC_mu_13, AC_mu_23, AC_mu_33, AC_mu_43, AC_mu_53),
  AC_sd_3 = round(c(AC_sd_13, AC_sd_23, AC_sd_33, AC_sd_43, AC_sd_53), 2),
  AC_mu_4 = c(AC_mu_14, AC_mu_24, AC_mu_34, AC_mu_44, AC_mu_54),
  AC_sd_4 = round(c(AC_sd_14, AC_sd_24, AC_sd_34, AC_sd_44, AC_sd_54), 2),
  time_mu_1 = round(c(time_mu_11, time_mu_21, time_mu_31, time_mu_41, time_mu_51), 4),
  time_sd_1 = round(c(time_sd_11, time_sd_21, time_sd_31, time_sd_41, time_sd_51), 4),
  time_mu_2 = round(c(time_mu_12, time_mu_22, time_mu_32, time_mu_42, time_mu_52), 4),
  time_sd_2 = round(c(time_sd_12, time_sd_22, time_sd_32, time_sd_42, time_sd_52), 4),
  time_mu_3 = round(c(time_mu_13, time_mu_23, time_mu_33, time_mu_43, time_mu_53), 4),
  time_sd_3 = round(c(time_sd_13, time_sd_23, time_sd_33, time_sd_43, time_sd_53), 4),
  time_mu_4 = round(c(time_mu_14, time_mu_24, time_mu_34, time_mu_44, time_mu_54), 4),
  time_sd_4 = round(c(time_sd_14, time_sd_24, time_sd_34, time_sd_44, time_sd_54), 4)))

print(df)