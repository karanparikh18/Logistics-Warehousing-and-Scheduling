
param day_end;
param min_rental_duration;
param num_customers;
param num_vans;
param num_trucks;

param BigM := 10000;

set CUSTOMERS := 1..num_customers;
set LOCATIONS := {0} union CUSTOMERS;
set VANS := 1..num_vans;
set TRUCKS := num_vans+1..num_vans+num_trucks;
set VEHICLES := VANS union TRUCKS;

param van_capacity;
param truck_capacity;

param van_rental_cost;
param truck_rental_cost;

param mileage_cost;

param van_speed;
param truck_speed;

param service_time;
param due_times{CUSTOMERS};
param distance{LOCATIONS, LOCATIONS};

var rental_start{VEHICLES} >= 0;# integer;
var rental_end{VEHICLES} >= 0; #integer;
var arrival_time{LOCATIONS, VEHICLES} >= 0;
var traversed{LOCATIONS, LOCATIONS, VEHICLES} binary;

minimize TotalCost: sum{i in LOCATIONS, j in LOCATIONS, k in VEHICLES:i<>j} mileage_cost * (if i < j then distance[i,j] else distance[j,i]) * traversed[i,j,k] +
					sum{k in VANS} van_rental_cost * (rental_end[k] - rental_start[k]) + 
					sum{k in TRUCKS} truck_rental_cost * (rental_end[k] - rental_start[k]);
					
subject to
	
	#all customers must be visited by exactly one vehicle
	AllPackagesDelivered {i in CUSTOMERS}: 
		sum{j in LOCATIONS, k in VEHICLES: j<>i} traversed[j,i,k] = 1;
	
	#a vehicle coming to a customer must go to another customer or to warehouse
	FlowBalance {i in CUSTOMERS, k in VEHICLES}:
		sum{j in LOCATIONS:i<>j} traversed[j,i,k] - sum{j in LOCATIONS:i<>j} traversed[i,j,k] = 0; 
	
	#a vehicle can go to only one customer. if traversed[0,0,k]=1, then the vehicle k is not used
	VehicleMovement {k in VEHICLES}:
		sum{j in LOCATIONS} traversed[0,j,k] = 1;
	
	#a vehicle cannot visit more customers than its capacity
	VehicleCapacity{k in VEHICLES}:
		sum{i in LOCATIONS, j in CUSTOMERS: j<>i} traversed[i,j,k] <= (if k <= num_vans then van_capacity else truck_capacity);
	
	#if a customer is visited right after the warehouse, then the arrival time is at least (rental start time + travel time)
	ArrivalTime0 {j in CUSTOMERS, k in VEHICLES}:
		arrival_time[j,k] + (1 - traversed[0,j,k]) * BigM 
				- (rental_start[k] * 60 + distance[0,j] * 60 / (if k <= num_vans then van_speed else truck_speed)) >= 0;
	
	#if a customer is visited after another customer, then the arrival time is at least (delivery completion time + travel time)	
	ArrivalTime {i in CUSTOMERS, j in LOCATIONS, k in VEHICLES : i<>j}:
		arrival_time[j,k] + (1 - traversed[i,j,k]) * BigM 
				- (arrival_time[i,k] + service_time + (if i < j then distance[i,j] else distance[j,i]) * 60 / (if k <= num_vans then van_speed else truck_speed)) >= 0;
	
	#vehicles must return to the warehouse before their rental end time
	WarehouseReturnTime {k in VEHICLES}:
		arrival_time[0,k] <= 60 * rental_end[k];
	
	#rental end time can be at most end of the day
	MaxRentalEnd {k in VEHICLES}:
		rental_end[k] <= day_end;
	
	#all packages must be delivered by their due times
	DueTime {i in CUSTOMERS}:
		sum {k in VEHICLES} arrival_time[i,k] + service_time <= due_times[i];
	
	#if a vehicle is used, then its rental duration must be at least minimum rental duration (3 hours)
	RentalDurationLength {k in VEHICLES}:
		rental_end[k] - rental_start[k] >= min_rental_duration * (1 - traversed[0,0,k]); 
		
		
		
		
		
		
		