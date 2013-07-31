cd <- function(dir = tclvalue(tkchooseDirectory()), saveOld = FALSE, clear = FALSE, loadNew = FALSE) {
  require(tcltk, quietly = TRUE)
  if (saveOld) save.image(compress = TRUE)
  setwd(dir)
  if (clear) rm(list = ls(all = TRUE, envir = .GlobalEnv), envir = .GlobalEnv)
  if (loadNew && file.exists(".RData")) {
    loaded <- load(".RData", envir = .GlobalEnv)
    return(invisible(loaded))
  }
}

new.func <- function()

color.name <- function(colorNumber) colors()[colorNumber]

overview <- function() {
  prop <- function(x)
    list(class = data.class(x), dim = dim(x), size = object.size(x), NAs = na.count(x))
  do.call("rbind", eapply(.GlobalEnv, prop))
}

na.count <- function(x) {
  if (is.vector(x)) return (sum(is.na(x)))
  if (is.data.frame(x) | is.matrix(x)) {
    col.count <- sapply(1:ncol(x), function(i) sum(is.na(x[, i])))
    names(col.count) <- colnames(x)
    col.count
  } else {
    NA
  }
}

copy.lower.to.upper <- function(mat) {
  if (!is.matrix(mat)) mat <- as.matrix(mat)
  if (nrow(mat) != ncol(mat)) stop("Matrix is not square.")
  new.mat <- mat
  for (row in 1:(nrow(mat) - 1)) {
    for (col in (row + 1):nrow(mat)) new.mat[row, col] <- mat[col, row]
  }
  new.mat
}

copy.upper.to.lower <- function(mat) {
  if (!is.matrix(mat)) mat <- as.matrix(mat)
  if (nrow(mat) != ncol(mat)) stop("Matrix is not square.")
  new.mat <- mat
  for (row in 1:(nrow(mat) - 1)) {
    for (col in (row + 1):nrow(mat)) new.mat[col, row] <- mat[row, col]
  }
  new.mat
}

ci.range <- function(pct) {
  if((pct < 0) | (pct > 100)) return(NA)
  if(pct > 1) pct <- pct / 100
  lci <- (1 - pct) / 2
  uci <- 1 - lci
  c(lci, uci)
}

odds <- function(pct) ifelse(pct < 0 | pct > 1, NA, pct / (1 - pct))
log.odds <- function(pct) log(odds(pct))
inv.odds <- function(odds) odds / (1 + odds)
inv.log.odds <- function(log.odds) exp(log.odds) / (1 + exp(log.odds))

uniform.test <- function(hist.output, B = NULL) {
  break.diff <- diff(hist.output$breaks)
  probs <- break.diff / sum(break.diff)
  if (is.null(B)) {
    chisq.test(x = hist.output$counts, p = probs)
  } else {
    chisq.test(x = hist.output$counts, p = probs, simulate.p.value = TRUE, B = B)
  }
}

affin.prop <- function(sim.mat, num.iter = 100, stable.iter = 10, shared.pref = "min", lambda = 0.5) {
  #
  # Affinity Propagation following :
  #   Frey, B.J., and D. Dueck.  2007.  Clustering by passing messges between data points.  Science 315:972-976.
  #
  # Eric Archer (eric.archer@noaa.gov)
  # 5/16/2007
  #

  # check similarity matrix structure
  if (!is.matrix(sim.mat)) sim.mat <- as.matrix(sim.mat)
  if (nrow(sim.mat) != ncol(sim.mat)) {
    warning("sim.mat is not square - NA returned")
    return(NA)
  } 

  # calculate shared preferences (resp[k,k])
  if (is.character(shared.pref)) {
    if (shared.pref == "median") diag(sim.mat) <- median(sim.mat[lower.tri(sim.mat)])
    if (shared.pref == "min") diag(sim.mat) <- min(sim.mat[lower.tri(sim.mat)])
  }
  if (is.numeric(shared.pref)) diag(sim.mat) <- shared.pref

  # setup matrices
  n <- nrow(sim.mat)
  avail <- resp <- matrix(0, nrow = n, ncol = n)
  max.k.mat <- matrix(NA, nrow = n, ncol = num.iter)

  for (iter in 1:num.iter) {
    # update responsibilities
    prop.resp <- sapply(1:n, function(k) {
      sapply(1:n, function(i) sim.mat[i, k] - max(avail[i, -k] + sim.mat[i, -k]))
    })
    resp <- (resp * lambda) + (prop.resp * (1 - lambda))

    # update availabilities    
    prop.avail <- sapply(1:n, function(k) {
      sapply(1:n, function(i) {
        if (k == i) {
          resp.other.points <- resp[-i, k]
          resp.other.points <- resp.other.points[resp.other.points > 0]
          sum(resp.other.points)
        } else {
          resp.other.points <- resp[-c(i, k), k]
          resp.other.points <- resp.other.points[resp.other.points > 0]
          min(0, resp[k, k] + sum(resp.other.points))
        }
      })
    })
    avail <- (avail * lambda) + (prop.avail * (1 - lambda))

    # find exemplars
    avail.resp.sum <- avail + resp
    max.k <- sapply(1:n, function(i) which.max(avail.resp.sum[i, ]))    

    # check if stable in last 'stable.iter' iterations
    max.k.mat[, iter] <- max.k
    if (iter >= stable.iter) {
      cols <- (iter - stable.iter):iter
      stable <- sapply(1:nrow(max.k.mat), function(row) length(unique(max.k.mat[row, cols])) == 1)
      if (all(stable)) {
        max.k.mat <- matrix(max.k.mat[, 1:iter], nrow = n, ncol = iter)
        break
      }
    }
  }

  rownames(max.k.mat) <- rownames(sim.mat)
  max.k.mat
}


clean.rf.data <- function(x, y, data, max.levels = 30) {
  x <- setdiff(x, y)
  sub.df <- data[, c(y, x)]
  sub.df <- sub.df[complete.cases(sub.df), , drop = TRUE]
  
  delete.pred <- character(0)
  for (pred in x) {
    pred.vec <- sub.df[[pred]]
    if (length(unique(pred.vec)) == 0) delete.pred <- c(delete.pred, pred)
    if (is.factor(pred.vec) & (nlevels(pred.vec) > max.levels)) delete.pred <- c(delete.pred, pred)
  }
  delete.pred <- unique(delete.pred)
  if (length(delete.pred) > 0) x <- setdiff(x, delete.pred)

  if (is.factor(sub.df[[y]]) & nlevels(sub.df[[y]][, drop = TRUE]) < 2) return(NULL)
  sub.df[, c(y, x)]
}

lat.lon.axes <- function(lon.range, lat.range, lon.n = 5, lat.n = 5) {
  lon <- list(ticks = pretty(lon.range, n = lon.n))
  lon$labels <- parse(text = sapply(lon$ticks, function(i) {
    a <- ifelse(i <= 0, -1 * i, i)
    b <- ifelse(i <= 0, "W", "E")
    paste(a, "*degree~", b, sep = "")
  }))
  
  lat <- list(ticks = pretty(lat.range, n = lat.n))
  lat$labels <- parse(text = sapply(lat$ticks, function(i) {
    a <- ifelse(i <= 0, -1 * i, i)
    b <- ifelse(i <= 0, "S", "N")
    paste(a, "*degree~", b, sep = "")
  }))
  
  axis(1, at = lon$ticks, labels = lon$labels)
  axis(2, at = lat$ticks, labels = lat$labels, las = 1)
  axis(3, at = lon$ticks, labels = lon$labels)
  axis(4, at = lat$ticks, labels = lat$labels, las = 1)
}

plot.samples <- function(df, lon.range, lat.range, main = NULL, pch = 19, pt.cex = 1, col = "black") {
  stopifnot(require(maps, quietly = TRUE))
  stopifnot(require(mapdata, quietly = TRUE))
  has.loc <- !is.na(df$latitude) & !is.na(df$longitude) 
  in.lon.range <- df$longitude >= min(lon.range) & df$longitude <= max(lon.range)
  in.lat.range <- df$latitude >= min(lat.range) & df$latitude <= max(lat.range)
  to.plot <- has.loc & in.lon.range & in.lat.range

  if(!is.null(main)) main <- paste(main, " (n = ", sum(to.plot), ")", sep = "")
  if(length(pch) == nrow(df)) pch <- pch[to.plot]
  if(length(pt.cex) == nrow(df)) pt.cex <- pt.cex[to.plot]
  if(length(col) == nrow(df)) col <- col[to.plot]

  op <- par(mar = c(3, 5, 5, 5) + 0.1, oma = c(2, 2, 2, 2))
  map("worldHires", fill = TRUE, col = "wheat3", xlim = lon.range, ylim = lat.range)
  points(df$longitude[to.plot], df$latitude[to.plot], pch = pch, cex = pt.cex, col = col, bg = col)

  lat.lon.axes(lon.range, lat.range)
  
  if(!is.null(main)) mtext(main, line = 3, cex = 1.5)
  box()
  par(op)
}


normalize <- function(x) (x - mean(x, na.rm = TRUE)) / sd(x, na.rm = TRUE)


# -- Geodesic functions --

as.radians <- function(degrees) degrees * pi / 180
as.degrees <- function(radians) radians * 180 / pi
as.bearing <- function(radians) (as.degrees(radians) + 360) %% 360

as.km <- function(distance, dist.units) {
  switch(dist.units,
         km = distance,
         nm = distance * 1.852,
         mi = distance * 1.609344,
         NA
  )
}

as.nm <- function(distance, dist.units) {
  switch(dist.units,
         km = distance * 0.539956803,
         nm = distance,
         mi = distance * 0.868976242,
         NA
  )
}

as.mi <- function(distance, dist.units) {
  switch(dist.units,
         km = distance * 0.621371192,
         nm = distance * 1.150779448,
         mi = distance,
         NA
  )
}


calc.bearing <- function(lat1, lon1, lat2, lon2) {
  # lat: latitude (numeric vector)
  if(any(is.na(c(lat1, lon1, lat2, lon2)))) return(NA)
  lat1 <- as.radians(lat1)
  lon1 <- as.radians(lon1)
  lat2 <- as.radians(lat2)
  lon2 <- as.radians(lon2)   
  delta.l <- lon2 - lon1
  term1 <- cos(lat1) * sin(lat2)
  term2 <- sin(lat1) * cos(lat2) * cos(delta.l)
  term3 <- sin(delta.l) * cos(lat2)
  as.bearing(atan2(term1 - term2, term3))
}


datum <- function(model = "WGS84") {
  # model : choice of ellipsoid model ("WGS84", "GRS80", "Airy", "International", "Clarke", "GRS67")
  # parameters based on distances in km
  switch(model,
         WGS84 = c(a = 6378137, b = 6356752.3142, f = 1 / 298.257223563),
         GRS80 = c(a = 6378137, b = 6356752.3141, f = 1 / 298.257222101),
         Airy = c(a = 6377563.396, b = 6356256.909, f = 1 / 299.3249646),
         International = c(a = 6378888, b = 6356911.946, f = 1 / 297),
         Clarke = c(a = 6378249.145, b = 6356514.86955, f = 1 / 293.465),
         GRS67 = c(a = 6378160, b = 6356774.719, f = 1 / 298.25),
         c(a = NA, b = NA, f = NA)
  )
}


destination.sphere <- function(lat, lon, brng, distance, dist.units = "nm", radius = as.nm(6371, "km")) {
  # lat, lon : lattitude and longitude in decimal degrees
  # brng : bearing from 0 to 360 degrees
  # dist : distance travelled
  # dist.units : units of distance ("km" (kilometers), "nm" (nautical miles), "mi" (statute miles))
  # radius : radius of sphere in dist.units
  # 
  # Code adapted from JavaScript by Chris Veness (scripts@movable-type.co.uk)
  #   at http://www.movable-type.co.uk/scripts/latlong.html#ellipsoid
  # Originally from Ed Williams' Aviation Formulary, http://williams.best.vwh.net/avform.htm#LL
  #
  #
  
  if(any(is.na(c(lat, lon, brng, distance)))) return(NA)
  lat <- as.radians(lat)
  lon <- as.radians(lon)
  brng <- as.radians(brng)
  
  psi <- distance / radius
  lat2 <- asin(sin(lat) * cos(psi) +  cos(lat) * sin(psi) * cos(brng))
  lon2 <- lon + atan2(sin(brng) * sin(psi) * cos(lat), cos(psi) - sin(lat) * sin(lat2))
  if (is.nan(lat2) || is.nan(lon2)) return(c(lat = NA, lon = NA))
  c(lat = as.degrees(as.numeric(lat2)), lon = as.degrees(as.numeric(lon2)))
}


destination.ellipsoid <- function(lat, lon, brng, distance, dist.units = "nm", ellipsoid = datum()) {
  # lat, lon : lattitude and longitude in decimal degrees
  # brng : bearing from 0 to 360 degrees
  # dist : distance travelled
  # dist.units : units of distance ("km" (kilometers), "nm" (nautical miles), "mi" (statute miles))
  # ellipsoid : ellipsoid model parameters - output from 'datum' call
  # 
  # Code adapted from JavaScript by Larry Bogan (larry@go.ednet.ns.ca)
  #   at http://www.go.ednet.ns.ca/~larry/bsc/jslatlng.html
  #
  #
  
  if(any(is.na(c(lat, lon, brng, distance)))) return(NA)
  distance <- as.km(distance, dist.units)
  lat <- as.radians(lat)
  lon <- as.radians(lon)
  brng <- as.radians(brng)
  e <- 0.08181922
  
  radius <- (ellipsoid["a"] / 1000) * (1 - e ^ 2) / ((1 - e ^ 2 * sin(lat) ^ 2) ^ 1.5)
  psi <- distance / radius
  phi <- pi / 2 - lat
  arc.cos <- cos(psi) * cos(phi) + sin(psi) * sin(phi) * cos(brng)
  lat2 <- as.degrees(as.numeric((pi / 2) - acos(arc.cos)))
  
  arc.sin <- sin(brng) * sin(psi) / sin(phi)
  lon2 <- as.degrees(as.numeric(lon + asin(arc.sin)))
  
  c(lat = lat2, lon = lon2)
}


destination.Vincenty <- function(lat, lon, brng, distance, dist.units = "nm", ellipsoid = datum()) {
  # lat, lon : lattitude and longitude in decimal degrees
  # brng : bearing from 0 to 360 degrees
  # dist : distance travelled
  # dist.units : units of distance ("km" (kilometers), "nm" (nautical miles), "mi" (statute miles))
  # ellipsoid : ellipsoid model parameters - output from 'datum' call
  # 
  # Code adapted from JavaScript by Chris Veness (scripts@movable-type.co.uk)
  #   at http://www.movable-type.co.uk/scripts/latlong-vincenty-direct.html
  # Original reference (http://www.ngs.noaa.gov/PUBS_LIB/inverse.pdf):
  #   Vincenty, T. 1975.  Direct and inverse solutions of geodesics on the
  #      ellipsoid with application of nested equations. Survey Review 22(176):88-93
  #
  #
  
  if(any(is.na(c(lat, lon, brng, distance)))) return(NA)
  distance <- as.km(distance, dist.units) * 1000
  lat <- as.radians(lat)
  lon <- as.radians(lon)
  brng <- as.radians(brng)
  
  sin.alpha1 <- sin(brng)
  cos.alpha1 <- cos(brng)
  tan.u1 <- (1 - ellipsoid["f"]) * tan(lat)
  cos.u1 <- 1 / sqrt(1 + (tan.u1 ^ 2))
  sin.u1 <- tan.u1 * cos.u1
  sigma1 <- atan2(tan.u1, cos.alpha1)
  sin.alpha <- cos.u1 * sin.alpha1
  cos.sq.alpha <- 1 - (sin.alpha ^ 2)
  u.sq <- cos.sq.alpha * ((ellipsoid["a"] ^ 2) - (ellipsoid["b"] ^ 2)) / (ellipsoid["b"] ^ 2)
  cap.A <- 1 + u.sq / 16384 * (4096 + u.sq * (-768 + u.sq * (320 - 175 * u.sq)))
  cap.B <- u.sq / 1024 * (256 + u.sq * (-128 + u.sq * (74 - 47 * u.sq)))
  
  sigma <- distance / (ellipsoid["b"] * cap.A)
  sigma.p <- 2 * pi
  cos.2.sigma.m <- cos(2 * sigma1 + sigma)
  while(abs(sigma - sigma.p) > 1e-12) {
    cos.2.sigma.m <- cos(2 * sigma1 + sigma)
    sin.sigma <- sin(sigma)
    cos.sigma <- cos(sigma)
    delta.sigma <- cap.B * sin.sigma * (cos.2.sigma.m + cap.B / 4 * (cos.sigma *
                                                                       (-1 + 2 * cos.2.sigma.m ^ 2) - cap.B / 6 * cos.2.sigma.m * 
                                                                       (-3 + 4 * sin.sigma ^ 2) * (-3 + 4 * cos.2.sigma.m ^ 2)))
    sigma.p <- sigma
    sigma <- distance / (ellipsoid["a"] * cap.A) + delta.sigma
  }
  
  tmp <- sin.u1 * sin.sigma - cos.u1 * cos.sigma * cos.alpha1
  lat2 <- atan2(sin.u1 * cos.sigma + cos.u1 * sin.sigma * cos.alpha1, 
                (1 - ellipsoid["f"]) * sqrt(sin.alpha ^ 2 + tmp ^ 2))
  lambda <- atan2(sin.sigma * sin.alpha1, cos.u1 * cos.sigma - sin.u1 * sin.sigma * cos.alpha1)
  cap.C <- ellipsoid["f"] / 16 * cos.sq.alpha * (4 + ellipsoid["f"] * (ellipsoid["f"] - 3 * cos.sq.alpha))
  cap.L <- lambda - (1 - cap.C) * ellipsoid["f"] * sin.alpha *
    (sigma + cap.C * sin.sigma * (cos.2.sigma.m + cap.C * cos.sigma * (-1 + 2 * cos.2.sigma.m ^ 2)))
  
  c(lat = as.degrees(as.numeric(lat2)), lon = as.degrees(as.numeric(lon + cap.L)))
}


distance.LawOfCosines <- function(lat1, lon1, lat2, lon2, radius = as.nm(6371, "km")) {
  # lat, lon : lattitude and longitude in decimal degrees
  # radius : radius of sphere in dist.units
  #
  # Code adapted from JavaScript by Chris Veness (scripts@movable-type.co.uk)
  #   at http://www.movable-type.co.uk/scripts/latlong.html
  #
  #
  if(any(is.na(c(lat1, lon1, lat2, lon2)))) return(NA)
  delta.lon <- as.radians(lon2 - lon1)
  lat1 <- as.radians(lat1)
  lat2 <- as.radians(lat2)
  inner.term <- sin(lat1) * sin(lat2) + cos(lat1) * cos(lat2) * cos(delta.lon)
  sapply(inner.term, function(i) ifelse(i < -1 || i > 1, 0, acos(i) * radius))
}


distance.Haversine <- function(lat1, lon1, lat2, lon2, radius = as.nm(6371, "km")) {
  # lat, lon : lattitude and longitude in decimal degrees
  # radius : radius of sphere in dist.units
  #
  # Code adapted from JavaScript by Chris Veness (scripts@movable-type.co.uk)
  #   at http://www.movable-type.co.uk/scripts/latlong.html
  #
  #
  if(any(is.na(c(lat1, lon1, lat2, lon2)))) return(NA)
  delta.lat <- as.radians(lat2 - lat1)
  delta.lon <- as.radians(lon2 - lon1)
  lat1 <- as.radians(lat1)
  lat2 <- as.radians(lat2)
  term.a <- sin(delta.lat / 2) ^ 2 + cos(lat1) * cos(lat2) * sin(delta.lon / 2) ^ 2
  term.c <- 2 * atan2(sqrt(term.a), sqrt(1 - term.a))
  radius * term.c
}


distance.Vincenty <- function(lat1, lon1, lat2, lon2, dist.units = "nm", ellipsoid = datum(), 
                              iter.limit = 20) {
  # lat, lon : lattitude and longitude in decimal degrees
  # dist.units : units of distance ("km" (kilometers), "nm" (nautical miles), "mi" (statute miles))
  # ellipsoid : ellipsoid model parameters - output from 'datum' call
  #
  # Code adapted from JavaScript by Chris Veness (scripts@movable-type.co.uk)
  #   at http://www.movable-type.co.uk/scripts/latlong-vincenty.html
  # Original reference (http://www.ngs.noaa.gov/PUBS_LIB/inverse.pdf):
  #   Vincenty, T. 1975.  Direct and inverse solutions of geodesics on the
  #      ellipsoid with application of nested equations. Survey Review 22(176):88-93
  #
  #
  
  if(any(is.na(c(lat1, lon1, lat2, lon2)))) return(NA)
  lat1 <- as.radians(lat1)
  lon1 <- as.radians(lon1)
  lat2 <- as.radians(lat2)
  lon2 <- as.radians(lon2)
  delta.l <- lon2 - lon1
  u1 <- atan((1 - ellipsoid["f"]) * tan(lat1))
  u2 <- atan((1 - ellipsoid["f"]) * tan(lat2))
  sin.u1 <- sin(u1)
  cos.u1 <- cos(u1)
  sin.u2 <- sin(u2)
  cos.u2 <- cos(u2)
  
  lambda <- delta.l
  lambda.p <- 2 * pi
  iter <- 1
  while((abs(lambda - lambda.p) > 1e-12) &  (iter <= iter.limit)) {
    sin.lambda <- sin(lambda)
    cos.lambda <- cos(lambda)
    sin.sigma <- sqrt((cos.u2 * sin.lambda) * (cos.u2 * sin.lambda) +
                        (cos.u1 * sin.u2 - sin.u1 * cos.u2 * cos.lambda) *
                        (cos.u1 * sin.u2 - sin.u1 * cos.u2 * cos.lambda))
    if(sin.sigma == 0) return(0)
    cos.sigma <- sin.u1 * sin.u2 + cos.u1 * cos.u2 * cos.lambda
    sigma <- atan2(sin.sigma, cos.sigma)
    sin.alpha <- cos.u1 * cos.u2 * sin.lambda / sin.sigma
    cos.sq.alpha <- 1 - sin.alpha ^ 2
    cos.2.sigma.m <- cos.sigma - 2 * sin.u1 * sin.u2 / cos.sq.alpha
    if(is.nan(cos.2.sigma.m)) cos.2.sigma.m <- 0
    term.c <- ellipsoid["f"] / 16 * cos.sq.alpha * (4 + ellipsoid["f"] * (4 - 3 * cos.sq.alpha))
    lambda.p <- lambda
    lambda <- delta.l + (1 - term.c) * ellipsoid["f"] * sin.alpha * (sigma + term.c * sin.sigma *
                                                                       (cos.2.sigma.m + term.c * cos.sigma * (-1 + 2 * cos.2.sigma.m * cos.2.sigma.m)))
    iter <- iter + 1
  }
  if(iter > iter.limit) return(NA)
  
  u.sq <- cos.sq.alpha * (ellipsoid["a"] ^ 2 - ellipsoid["b"] ^ 2) / (ellipsoid["b"] ^ 2)
  term.a <- 1 + u.sq / 16384 * (4096 + u.sq * (-768 + u.sq * (320 - 175 * u.sq)))
  term.b <- u.sq / 1024 * (256 + u.sq * (-128 + u.sq * (74 - 47 * u.sq)))
  delta.sigma <- term.b * sin.sigma * (cos.2.sigma.m + term.b / 4 *
                                         (cos.sigma * (-1 + 2 * cos.2.sigma.m ^ 2) - term.b / 6 * cos.2.sigma.m *
                                            (-3 + 4 * sin.sigma ^ 2) * (-3 + 4 * cos.2.sigma.m ^ 2)))
  term.s <- ellipsoid["b"] * term.a * (sigma - delta.sigma)
  term.s <- term.s / 1000
  as.numeric(switch(dist.units,
                    nm = as.nm(term.s, "km"),
                    km = term.s,
                    mi = as.mi(term.s, "km"),
                    NA
  ))
}


circle.earth.poly <- function(lat, lon, radius, brng.limits = 0, sides = 1, by.length = TRUE,
                              dist.units = "nm", destination.func = destination.ellipsoid, ellipsoid = datum()) {
  # Creates a polygon centered at lat, lon of radius.
  #   chord.len is the minimum length of the chords along the circle generated
  #   if num.sides is specified, then a polygon of that number of sides is generated instead
  #
  #                                                           
  brng.limits <- brng.limits - 90
  if(length(brng.limits) == 1) brng.limits <- c(brng.limits, 360 + brng.limits)
  brng.limits <- brng.limits %% 360
  if(brng.limits[2] < brng.limits[1]) brng.limits[2] <- brng.limits[2] + 360
  if(brng.limits[2] == brng.limits[1]) brng.limits[2] <- min(brng.limits) + 360
  circle <- max(brng.limits) - 360 == min(brng.limits)
  brng.vec <- if(by.length) {
    brng <- seq(brng.limits[1], brng.limits[2], 2 * asin(sides / 2 / radius))
  } else {
    brng <- seq(brng.limits[1], brng.limits[2], length.out = trunc(sides) + 1)
  }
  if(circle) brng.vec <- brng.vec[-length(brng.vec)]
  poly.arr <- t(sapply(brng.vec, function(brng) {    
    destination.func(lat = lat, lon = lon, brng = brng, distance = radius,
                     dist.units = dist.units, ellipsoid = ellipsoid)
  }))
  rbind(poly.arr, poly.arr[1, ])[, c("lon", "lat")]
}


simple.circle.earth.poly <- function(lat, lon, radius, brng.limits = 0, sides = 0.1, by.length = TRUE, 
                                     dist.func = distance.LawOfCosines) {
  # Creates a polygon specified by a location and radius.
  #   x, y : center of polygon
  #   radius : distance of points away from center
  #   brng.limits : if vector of 1 value, starting bearing in degrees for first point of circle.
  #     if vector of two values, start and end bearings of arc
  #   sides : either length of or number of sides along perimeter of polygon
  #   by.length : TRUE : 'sides' is length of sides, FALSE : 'sides' is number of sides
  #
  #           
  lat.dist <- dist.func(lat, lon, lat + 1, lon)
  lon.dist <- dist.func(lat, lon, lat, lon + 1)
  mean.dist <- (lat.dist + lon.dist) / 2
  radius <- radius / mean.dist 
  if(by.length) sides <- sides / mean.dist
  circle.poly(lon, lat, radius, brng.limits, sides, by.length)
}


circle.poly <- function(x, y, radius, brng.limits = 0, sides = 0.1, by.length = TRUE) {
  # Creates a polygon specified by a location and radius.
  #   x, y : center of polygon
  #   radius : distance of points away from center
  #   brng.limits : if vector of 1 value, starting bearing in degrees for first point of circle.
  #     if vector of two values, start and end bearings of arc
  #   sides : either length of or number of sides along perimeter of polygon
  #   by.length : TRUE : 'sides' is length of sides, FALSE : 'sides' is number of sides
  #
  #
  brng.limits <- brng.limits - 90
  if(length(brng.limits) == 1) brng.limits <- c(brng.limits, 360 + brng.limits)
  brng.limits <- brng.limits %% 360
  if(brng.limits[2] < brng.limits[1]) brng.limits[2] <- brng.limits[2] + 360
  if(brng.limits[2] == brng.limits[1]) brng.limits[2] <- min(brng.limits) + 360
  circle <- max(brng.limits) - 360 == min(brng.limits)
  brng.limits <- brng.limits * pi / 180
  brng.vec <- if(by.length) {
    brng <- seq(brng.limits[1], brng.limits[2], 2 * asin(sides / 2 / radius))
  } else {
    brng <- seq(brng.limits[1], brng.limits[2], length.out = trunc(sides) + 1)
  }
  if(circle) brng.vec <- brng.vec[-length(brng.vec)]
  poly.arr <- t(sapply(brng.vec, function(brng) {
    c(x = x + cos(brng) * radius, y = y - sin(brng) * radius)
  }))
  rbind(poly.arr, poly.arr[1, ])
}

get.lat.lon.list <- function(area.poly) {
  stopifnot(require(gpclib))
  list(lon = get.pts(area.poly)[[1]]$x, lat = get.pts(area.poly)[[1]]$y)
}

box.area <- function(lat, lon, box.size) {
  # Calculates the area of a box with the lower right corner at lat, lon and of box.size degrees
  #
  
  integrate.Vincenty <- Vectorize(function(lat, start.lon, end.lon) distance.Vincenty(lat, start.lon, lat, end.lon))
  nm <- integrate(integrate.Vincenty, lower = lat, upper = lat + box.size, start.lon = lon, end.lon = lon - box.size)$value
  nm * distance.Vincenty(lat, lon, lat, lon - box.size) / box.size
}
