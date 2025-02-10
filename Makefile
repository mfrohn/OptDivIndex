CC = g++

solver: 
	g++ -std=c++11 -D_REENTRANT -w -O3 -I${GUROBI_HOME}/include/ -L${GUROBI_HOME}/lib/ DivProblems.cpp -o solver -lgurobi_c++ -lgurobi95
	
clean:	
	rm -f solver;
	clear;
