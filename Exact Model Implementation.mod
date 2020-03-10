/*********************************************
 * OPL 12.10.0.0 Model
 * Author: Greatmar2
 * Creation Date: Mar 4, 2020 at 1:16:53 PM
 *********************************************/

// Parameters
//int numStores = ...;
//int numHorses = ...;
//int numTrailers = ...;

{string} locations = ...;
{string} stores = ...;
{string} horses = ...;
{string} trailers = ...;
//range locations = 0..numStores+1;
//range stores = 1..numStores;
/*
range stores = 1..numStores;
range locations = stores;
execute ADD {
  locations.add(0);
  locations.add(numStores+1);
}
*/
//range horses = 1..numHorses;
//range trailers = 1..numTrailers;

float distances[locations][locations] = ...;
float times[locations][locations] = ...;
float distanceCost[horses] = ...;
float timeCost[horses] = ...;
int palletCapacity[trailers] = ...;
int horseTrailerCompatability[horses][trailers] = ...;
int storeHorseCompatability[stores][horses] = ...;
int storeTrailerCompatability[stores][trailers] = ...;
int demand[locations] = ...;
float windowStart[locations] = ...;
float windowEnd[locations] = ...;
float averageUnloadTime[locations] = ...;

float travelTimeConstMatrix[locations][locations];
float travelTimeConst = 24;
//travelTimeConst = max(i in windowEnd) - min(j in windowStart);

//Preprocessing
execute {
	for (var i in locations) {
	  for (var j in locations) {
	    travelTimeConstMatrix[i][j] = windowEnd[i] + (demand[i] * averageUnloadTime[i]) + times[i][i] - windowStart[j];
	  }
	}
}

//Variables
dvar boolean travel[locations][locations][horses];
dvar int+ deliveries[locations][horses];
dvar boolean vehicles[horses][trailers];
dvar float+ serviceStart[locations][horses];
dvar float+ travelTime[locations][locations][horses];


//Objective function
minimize
//  sum(i in locations, j in locations, k in horses) (travel[i][j][k] * ((distanceCost[k] * distances[i][j]) + 
//  	(travel[i][j][k] * timeCost[k] * (serviceStart[j][k] - serviceStart[i][k]))));
//  sum(i in locations, j in locations, k in horses) (travel[i][j][k] * distanceCost[k] * distances[i][j]);
	sum(i in locations, j in locations, k in horses) ((travel[i][j][k] * distanceCost[k] * distances[i][j]) + 
  		travelTime[i][j][k]);


//Constraints
subject to {
//  forall(i in locations, j in locations, k in horses)
//    ctTravelBool:
//    	travel[i][j][k] in {0, 1};
  forall (j in stores)
    // Meet Store's demand 
  	ctDemand:
  		sum(k in horses) deliveries[j][k] == demand[j];
//  forall (l in trailers) {
  forall (k in horses) {
    // Account for how many pallets must be loaded at depot
    ctLoad:
    	deliveries["Depot"][k] == sum(j in stores) deliveries[j][k];
    // Trailers must not "deliver" any pallets to the depot
    ctReturnEmpty:
    	deliveries["DepotReturn"][k] == 0; 
    // Prevent vehicles from delivering more than their maximum capacity (and only allow vehicles with a horse and trailer to deliver)
    ctCapacity:
    	deliveries["Depot"][k] <= sum(l in trailers) (palletCapacity[l]* vehicles[k][l]);
    // Only allow horses to be paired with compatable trailers
    forall (l in trailers)
      ctVehicleCompat:
      	vehicles[k][l] <= horseTrailerCompatability[k][l]; 
    // Only allow horses to be assigned to one or less trailers
    ctVehicles:
    	sum(l in trailers) vehicles[k][l] <= 1;
    forall (j in stores) {
      // Only allow vehicles to deliver to stores if both the trailer and horse are compatable with the store
      ctStoreCompat:
      	deliveries[j][k] <= demand[j] * sum(i in locations) (travel[i][j][k]) * storeHorseCompatability[j][k] * sum(l in trailers) (vehicles[k][l] * storeTrailerCompatability[j][l]);
	  //Make sure deliveries are >= 0
//	  ctPositive:
//	 	deliveries[j][k] >= 0;
    }
//  }   
//  forall (k in horses) {
    // Make sure paired vehicles leave the depot
    ctLeave:
//    	sum(j in locations: j != "Depot") (travel["Depot"][j][k]) - sum(l in trailers) (vehicles[k][l]) == 0;
    	sum(j in stores) (travel["Depot"][j][k]) - sum(l in trailers) (vehicles[k][l]) == 0;
    ctNoReturn: 
    	sum(i in locations) (travel[i]["Depot"][k]) == 0;
    // Make sure paired vehicles return
    ctReturn:
//    	sum(i in locations: i != "DepotReturn") (travel[i]["DepotReturn"][k]) - sum(l in trailers) (vehicles[k][l]) == 0;
    	sum(i in stores) (travel[i]["DepotReturn"][k]) - sum(l in trailers) (vehicles[k][l]) == 0;
    ctNoLeave: 
    	sum(j in locations) (travel["DepotReturn"][j][k]) == 0;
    // Make sure that vehicles leave stores that they arrive at
    forall(j in stores) 
    	ctMove:
    		sum(i in locations: i != j) (travel[i][j][k]) - sum(i in locations) (travel[j][i][k]) == 0;
    forall(j in locations) {
      // Only start unloading during store windows
      ctWindowStart:
      	windowStart[j] <= serviceStart[j][k];
//      	windowStart[j] * (sum(i in locations) travel[i][j][k]) <= serviceStart[j][k];
      ctWindowEnd:
      	serviceStart[j][k] <= windowEnd[j];
//      	serviceStart[j][k] <= windowEnd[j] * (sum(i in locations) travel[i][j][k]);
      forall(i in locations) {
        // Account for the time a vehicle takes to unload at and travel from the previous store
        ctWindowTravelTime:
	      	serviceStart[i][k] + (deliveries[i][k] * averageUnloadTime[i]) + times[i][j] <=  
	      		serviceStart[j][k] + ((1 - travel[i][j][k]) * travelTimeConstMatrix[i][j]);
//	      	serviceStart[i][k] + (deliveries[i][k] * averageUnloadTime[i]) + times[i][j] - windowEnd[j] <= 
//	      		(1 - travel[i][j][k]) * travelTimeConstMatrix[i][j];
//	      	serviceStart[i][k] + sum(l in trailers) (deliveries[i][l] * averageUnloadTime[i]) + times[i][j] - windowEnd[j] <= 
//	      		(1 - travel[i][j][k]) * travelTimeConstMatrix[i][j];
	     // Travel time matrix must either be difference between unload start times or zero
      	ctTravelTimeLess:
      		travelTime[i][j][k] <= abs(serviceStart[j][k] - serviceStart[i][k]);
      	ctTravelTimeGreater:
      		travelTime[i][j][k] >= serviceStart[j][k] - serviceStart[i][k] - (24*(1-travel[i][j][k]));
      	ctTravelTimeFloor:
      		travelTime[i][j][k] <= travelTimeConst*travel[i][j][k];
//      	ctTravelTimeNonnegative:
//      		travelTime[i][j][k] >= 0;
      }      		
    }
  }
};


//Post processing
execute {
  var outputFile = new IloOplOutputFile("Model Output.txt");
  outputFile.writeln("Data:");
  for(var k in horses) {
    for (var l in trailers) {
      if (vehicles[k][l] == 1) {
        outputFile.writeln("");
        outputFile.writeln("Horse " + k + " is paired with trailer " + l + ", with capacity " + palletCapacity[l]);
      }
    }
    for (var i in locations) {
      for (var j in locations) {
        if (travel[i][j][k] == 1) {
          outputFile.writeln("Horse " + k + " travels from " + i + " to " + j + " to deliver " + deliveries[j][k] + " pallets. Expected unload start time is " + serviceStart[j][k]);
        }
      }
    }
  }
//  for (var l in trailers) {
//    if (deliveries["Depot"][l] > 0) {
//      outputFile.writeln("Trailer " + l + " loads " + deliveries["Depot"][l] + " pallets at depot.");
//    }
//    for (var j in stores) {
//      if (deliveries[j][l] > 0) {
//        outputFile.writeln("Trailer " + l + " carries " + deliveries[j][l] + " pallets for " + j);
//      }
//    }     
//  }        
  outputFile.close();
}