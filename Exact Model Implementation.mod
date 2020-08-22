/*********************************************
 * OPL 12.10.0.0 Model
 * Author: Greatmar2
 * Creation Date: Mar 4, 2020 at 1:16:53 PM
 *********************************************/

// Parameters
//int numStores = ...;
//int numHorses = ...;
//int numTrailers = ...;
//int numVehicles = ...;

{string} locations = ...;
{string} customers = ...;
{string} vehicles = ...;
//{string} vehicleTypes = ...;
//range locations = 0..numStores+1;
//range customers = 1..numStores;
/*
range customers = 1..numStores;
range locations = customers;
execute ADD {
  locations.add(0);
  locations.add(numStores+1);
}
*/
//range horses = 1..numHorses;
//range trailers = 1..numTrailers;
//range vehicles = 1..numVehicles;

float coordinatesX[customers] = ...;
float coordinatesY[customers] = ...;
float distances[locations][locations] = ...;
float times[locations][locations] = ...;
float distanceCost[vehicles] = ...;
float timeCost[vehicles] = ...;
string vehicleTypes[vehicles] = ...;
int palletCapacity[vehicles] = ...;
int demand[locations] = ...;
float windowStart[locations] = ...;
float windowEnd[locations] = ...;
float averageUnloadTime[locations] = ...;

float travelTimeConstMatrix[locations][locations];
float travelTimeConst = 24;
//int vehicleCount = 0;
//travelTimeConst = max(i in windowEnd) - min(j in windowStart);

float beforeTime;

//Preprocessing
execute {
	for (var i in locations) {
	  for (var j in locations) {
	    travelTimeConstMatrix[i][j] = windowEnd[i] + (demand[i] * averageUnloadTime[i]) + times[i][i] - windowStart[j];
	  }
	}
	
//	for (var i in vehicleTypes) {
//	  for (var j in )
//	}
	
	beforeTime = (new Date()).getTime();
}

//execute PARAMS {
//  cplex.nodefileind = 3;
//}

//Variables
dvar boolean travel[locations][locations][vehicles];
dvar int+ deliveries[locations][vehicles];
dvar float+ serviceStart[locations][vehicles];
dvar float+ travelTime[locations][locations][vehicles];


//Objective function
minimize
	sum(i in locations, j in locations, k in vehicles) ((travel[i][j][k] * distanceCost[k] * distances[i][j]) + 
  		travelTime[i][j][k]);


//Constraints
subject to {
  forall (j in customers)
    // Meet Store's demand 
  	ctDemand:
  		sum(k in vehicles) (deliveries[j][k]) == demand[j];
  forall (k in vehicles) {
    // Account for how many pallets must be loaded at depot
    ctLoad:
    	deliveries["Depot"][k] == sum(j in customers) (deliveries[j][k]);
    // Vehicles must not "deliver" any pallets to the depot
    ctReturnEmpty:
    	deliveries["DepotReturn"][k] == 0; 
    // Vehicles must leave the depot if they are assigned to serve customers
    ctDepart:
    	deliveries["Depot"][k] <= palletCapacity[k] * sum(j in customers) travel["Depot"][j][k];
    // Make sure vehicles that leave the depot return to the depot
    ctReturn:
    	sum(j in customers) (travel["Depot"][j][k]) - sum(i in customers) (travel[i]["DepotReturn"][k]) == 0;
    // Vehicles may only depart from the depot once
    ctDepartOnce:
    	sum(j in customers) (travel["Depot"][j][k]) <= 1;
    // Vehicles should not return to the Depot
    ctNoReturn: 
    	sum(i in locations) (travel[i]["Depot"][k]) == 0;
    // Vehicles should not depart from "DepotReturn"
    ctNoDepart: 
    	sum(j in locations) (travel["DepotReturn"][j][k]) == 0;
    // Make sure that vehicles leave customers that they arrive at
    forall(j in customers) {
	    // Vehicles should not visit customers if they do not deliver
	    ctNoEmptyDelivery:
	    	sum(i in locations) travel[i][j][k] <= deliveries[j][k];
    	// Only service customer j with vehicle k if vehicle k travels to customer j, and only serve at most the vehicle capacity
    	restrictService: 
    		deliveries[j][k] <= palletCapacity[k] * sum(i in locations) travel[i][j][k];
    	// Vehicles should depart from customers as many times as it arrives at them
    	ctTravel:
    		sum(i in locations: i != j) (travel[i][j][k]) - sum(i in locations) (travel[j][i][k]) == 0;
   }    	
    forall(j in locations) {
      // Only start unloading during customer windows
      ctWindowStart:
      	windowStart[j] <= serviceStart[j][k];
      ctWindowEnd:
      	serviceStart[j][k] <= windowEnd[j];
      forall(i in locations) {
        // Account for the time a vehicle takes to unload at and travel from the previous customer
        ctWindowTravelTime:
	      	serviceStart[i][k] + (deliveries[i][k] * averageUnloadTime[i]) + times[i][j] <=  
	      		serviceStart[j][k] + ((1 - travel[i][j][k]) * travelTimeConstMatrix[i][j]);
	     // Travel time matrix must either be difference between unload start times or zero
      	ctTravelTimeGreater:
      		travelTime[i][j][k] >= serviceStart[j][k] - serviceStart[i][k] - (travelTimeConst*(1-travel[i][j][k]));
      }      		
    }
  }
};


//Post processing
execute {
  var afterTime = (new Date()).getTime();
  
  var outputFile = new IloOplOutputFile("Model Output.txt");
  
  //Input
  outputFile.writeln("Input:");
  for(var i in customers) {
//    outputFile.writeln("");
    outputFile.writeln("Customer " + i + " has " + demand[i] + " pallets demand and window " + windowStart[i] + "-" + windowEnd[i] + " at (" + coordinatesX[i] + ", " + coordinatesY[i] + ") and average unload time " + averageUnloadTime[i])
  }
  for (var k in vehicles) {
    outputFile.writeln("Vehicle " + k + " is a " + vehicleTypes[k] + " with capacity " + palletCapacity[k] + ", distance cost " + distanceCost[k] + ", and time cost " + timeCost[k]);
  }
  outputFile.writeln("");
  
  //Output
  outputFile.writeln("Output:");
  for(var k in vehicles) {
    for (var i in locations) {
      for (var j in locations) {
        if (travel[i][j][k] == 1) {
          outputFile.writeln("Vehicle " + k + " travels from " + i + " to " + j + " to deliver " + deliveries[j][k] + " pallets. Expected unload start time is " + serviceStart[j][k]);
        }
      }
    }
  }
//  for (var l in trailers) {
//    if (deliveries["Depot"][l] > 0) {
//      outputFile.writeln("Trailer " + l + " loads " + deliveries["Depot"][l] + " pallets at depot.");
//    }
//    for (var j in customers) {
//      if (deliveries[j][l] > 0) {
//        outputFile.writeln("Trailer " + l + " carries " + deliveries[j][l] + " pallets for " + j);
//      }
//    }     
//  }
  
  outputFile.writeln("");
  outputFile.writeln("Objective value: " + cplex.getObjValue());
//  outputFile.writeln("Solve time: " + cplex.getSolvedTime());
  outputFile.writeln("Solve time: " + (afterTime-beforeTime));
        
  outputFile.close();
}