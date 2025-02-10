#include <math.h>
#include <fstream>
#include <sstream>
#include <iostream>
#include <iomanip>
#include "gurobi_c++.h"
using namespace std;

int n,k,input_flag,remove_edge,n_edges;
double epsilon,theta,theta_ES;
string namefile;
ifstream in;
double **dist;
// cyclic contains a circular order of all taxa
int *cyclic;
// lower bounds for all taxa
double *LB;
// subset of k taxa
int **Y;
int n_Y;
// Variables for the LP
GRBEnv *env;
GRBModel *model;
GRBVar *y;
GRBVar *t;
GRBVar **edge_t;
// Equal Splits and Fair Proportion index scores
double *s_ES;
double *s_FP;
// variables for LP model constraints
double *edge_length;
int *X_length;
int **X;
double **gammaopt;
double total_length;
// taxa sets of optimal solutions
int **Yopt;



// defines distance matrix dist with ordering cyclic
void ReadDistanceMatrix(char * const fullnamefile){ 
	in.open(fullnamefile,std::ios::in); if(in.is_open()==false){cout << "Warning: Unable to open file. Please, try again."; exit(0);}
	cout<<"Reading distance matrix...";
	in >> n;
	cyclic = new int[n+2]; dist=new double*[n+2];
	for(register unsigned int i=1; i<=n+1; i++){in >> cyclic[i]; dist[i] = new double[n+2];} 
	for(register unsigned int i=1; i<=n+1; i++){
		in >> dist[i][i]; for(register unsigned int j=1; j<=n+1; j++) in >> dist[cyclic[i]][cyclic[j]];
	}
	in.close();	
	cout<<"done!"<<endl;
}

// defines lower bounds LB
void setBounds(){
	LB=new double[n+1];
	switch(input_flag){
		case 1:{
			LB[1]=1.156726382+2.118209966/2.0; LB[2]=3.249628377+0.09872726878/2.0; LB[3]=3.274936349; LB[4]=0.7002824983; LB[5]=0.9037960304; 
			LB[6]=LB[1]; LB[7]=0.4159185811+0.2843639171/2.0; LB[8]=3.348355645; LB[9]=LB[2]; LB[10]=LB[7]; 
			break;}
		case 2:{
			LB[1]=0.02718172184+0.01469498334/2.0; LB[2]=0.9931574887+0.7728564513/2.0+0.8239797465/4.0; LB[3]=LB[2]; LB[4]=1.20327307+1.386720616/2.0; 
			LB[5]=0.2228711889+0.5033645792/2.0; LB[6]=LB[5]; LB[7]=0.1401228362+1.127234247/2.0; LB[8]=LB[4]; LB[9]=LB[1]; LB[10]=0.4958372929+1.270176647/2.0+0.8239797465/4.0; 
			LB[11]=LB[7]; LB[12]=0.04187670519; LB[13]=LB[10]; LB[14]=0.7262357681; LB[15]=1.267357083; LB[16]=3.541643493; 
			break;}
		case 3:{
			LB[1]=0.615443024+0.3253610955/2.0; LB[2]=LB[1]; LB[3]=0.9408041194; LB[4]=2.104490702+1.526809943/2.0; LB[5]=LB[4]; LB[6]=4.564967492; 
			LB[7]=0.8192279641+0.6406104884/2.0; LB[8]=LB[7]; LB[9]=1.459838453; LB[10]=1.203463735+2.550903438/2.0; LB[11]=LB[10]; LB[12]=4.232416231+17.20698643/2.0; 
			LB[13]=LB[12]; LB[14]=1.527763453+0.4119492242/2.0; LB[15]=LB[14]; LB[16]=1.939712677; LB[17]=0.7109423624+6.060350191/2.0; LB[18]=LB[17]; 
			LB[19]=3.323274926+3.845034583/2.0; LB[20]=LB[19]; LB[21]=7.168309508; LB[22]=7.862120741;
			break;}
	}
}

void setConstraints(){
	edge_length=new double[n_edges+1]; X_length=new int[n_edges+1]; X=new int*[n_edges+1]; gammaopt=new double*[n_edges+1];
	switch(input_flag){
		case 1:{
			// define edge lengths
			edge_length[1]=4.853363685; edge_length[2]=0.2035135321; edge_length[3]=0.1255187229; edge_length[4]=0.1989380193;
			for(register unsigned int i=1; i<= n_edges; i++) if(i==remove_edge){edge_length[i]=0.000000001; break;}
			total_length=2.283285348; for(register unsigned int i=1; i<=n_edges; i++) total_length+=edge_length[i]; 
			// define subsets of taxa X[v]
			X_length[1]=4; X_length[2]=3; X_length[3]=3; X_length[4]=3;
			for(register unsigned int i=1; i<=n_edges; i++){X[i]=new int[X_length[i]+1]; gammaopt[i]=new double[X_length[i]+1];}
			X[1][1]=5; X[1][2]=4; X[1][3]=7; X[1][4]=10;
			X[2][1]=4; X[2][2]=7; X[2][3]=10;
			X[3][1]=2; X[3][2]=9; X[3][3]=8;
			X[4][1]=1; X[4][2]=6; X[4][3]=3;
			// epsilon = 0 for the RDDP, epsilon = 1/2 for the R3DP
			if(epsilon!=-1){
				cout << "set epsilon constraints"<<endl;
				model->addConstr(edge_t[1][5]<=(1-epsilon)*edge_length[1]);
				for(register unsigned int i=1; i<=X_length[2]; i++){
					model->addConstr(edge_t[1][X[2][i]]-edge_t[2][X[2][i]]<=(1-epsilon)*edge_length[1]);
					model->addConstr(edge_t[2][X[2][i]]<=(1-epsilon)*edge_length[2]);
					model->addConstr(edge_t[3][X[3][i]]<=(1-epsilon)*(edge_length[3]+2.283285348/2.0));
					model->addConstr(edge_t[4][X[4][i]]<=(1-epsilon)*(edge_length[4]+2.283285348/2.0));
				}
			}
			model->addConstr(edge_t[1][2]<=edge_length[3]/2.0+2.283285348/4.0);
			model->addConstr(edge_t[1][2]+edge_t[1][5]<=edge_length[3]/2.0+2.283285348/4.0+edge_length[1]);
			model->addConstr(edge_t[1][4]<=edge_length[1]-edge_t[1][5]+edge_length[2]*(1-edge_t[1][2]/(edge_length[3]/2.0+2.283285348/4.0)));
			model->addConstr(edge_t[1][7]<=(edge_length[1]-edge_t[1][5])/2.0+(edge_length[2]/2.0)*edge_t[1][2]/(edge_length[3]/2.0+2.283285348/4.0));
			model->addConstr(edge_t[1][5]+edge_t[1][4]+2*edge_t[1][7]==edge_length[1]+edge_length[2]);
			model->addConstr(edge_t[1][10]==edge_t[1][7]);
			// compatability constraints
			model->addConstr(edge_t[2][5]==0);
			model->addConstr(edge_t[2][4]==edge_length[2]*(1-edge_t[1][2]/(edge_length[3]/2.0+2.283285348/4.0)));
			model->addConstr(edge_t[2][7]==(edge_length[2]/2.0)*edge_t[1][2]/(edge_length[3]/2.0+2.283285348/4.0));
			model->addConstr(edge_t[2][10]==edge_t[2][7]);
			model->addConstr(edge_t[3][8]==(edge_length[3]+2.283285348/2.0)*(1-edge_t[1][2]/(edge_length[3]/2.0+2.283285348/4.0)));
			model->addConstr(edge_t[3][2]==edge_t[1][2]);
			model->addConstr(edge_t[3][9]==edge_t[3][2]);
			model->addConstr(edge_t[4][3]==(edge_length[4]+2.283285348/2.0)*(1-edge_t[1][2]/(edge_length[3]/2.0+2.283285348/4.0)));
			model->addConstr(edge_t[4][1]==(edge_length[4]/2.0+2.283285348/4.0)*edge_t[1][2]/(edge_length[3]/2.0+2.283285348/4.0));
			model->addConstr(edge_t[4][6]==edge_t[4][1]);
			if(theta!=-1){
				for(register unsigned int k=1; k<=n_edges; k++)
					for(register unsigned int i=1; i<=X_length[k]; i++)
						for(register unsigned int j=1; j<=X_length[k]; j++)
							if(i!=j){
								if(k==1) model->addConstr(y[X[k][i]]>=edge_t[k][X[k][i]]-edge_t[k+1][X[k][i]]-edge_t[k][X[k][j]]+edge_t[k+1][X[k][j]]);
								else model->addConstr(y[X[k][i]]>=edge_t[k][X[k][i]]-edge_t[k][X[k][j]]);
							}
				GRBLinExpr sum=0; for(register unsigned int i=1; i<=n; i++) sum+=y[i];
				model->addConstr(sum<=(1.0000001-theta)*total_length);
			}
			model->addConstr(t[1]==edge_t[4][1]); model->addConstr(t[2]==edge_t[3][2]);
			model->addConstr(t[3]==edge_t[4][3]); model->addConstr(t[4]==edge_t[1][4]);
			model->addConstr(t[5]==edge_t[1][5]); model->addConstr(t[6]==edge_t[4][6]);
			model->addConstr(t[7]==edge_t[1][7]); model->addConstr(t[8]==edge_t[3][8]);
			model->addConstr(t[9]==edge_t[3][9]); model->addConstr(t[10]==edge_t[1][10]);
			break;}
		case 2:{
			// define edge lengths
			edge_length[1]=0.8029194702; edge_length[2]=2.737294992; edge_length[3]=0.1891780108; 
			edge_length[4]=0.04044767411; edge_length[5]=2.025795591; edge_length[6]=2.566916906;
			for(register unsigned int i=1; i<= n_edges; i++) if(i==remove_edge){edge_length[i]=0.000000001; break;}
			total_length=0.2484908189; for(register unsigned int i=1; i<=n_edges; i++) total_length+=edge_length[i]; 
			// define subsets of taxa X[v]
			X_length[1]=9; X_length[2]=3; X_length[3]=6; X_length[4]=7; X_length[5]=3; X_length[6]=3;
			for(register unsigned int i=1; i<=n_edges; i++){X[i]=new int[X_length[i]+1]; gammaopt[i]=new double[X_length[i]+1];}
			X[1][1]=9; X[1][2]=1; X[1][3]=12; X[1][4]=4; X[1][5]=8; X[1][6]=13; X[1][7]=10; X[1][8]=2; X[1][9]=3;
			X[2][1]=9; X[2][2]=1; X[2][3]=12; X[3][1]=4; X[3][2]=8; X[3][3]=13; X[3][4]=10; X[3][5]=2; X[3][6]=3;
			X[4][1]=15; X[4][2]=7; X[4][3]=11; X[4][4]=5; X[4][5]=6; X[4][6]=14; X[4][7]=16;
			X[5][1]=15; X[5][2]=7; X[5][3]=11; X[6][1]=5; X[6][2]=6; X[6][3]=14;
			// epsilon = 0 for the RDDP, epsilon = 1/2 for the R3DP
			if(epsilon!=-1){
				for(register unsigned int k=1; k<=n_edges; k++)
					for(register unsigned int i=1; i<=X_length[k]; i++) 
						if(k<=4) model->addConstr(edge_t[k][X[k][i]]<=(1-epsilon)*edge_length[k]);
						else model->addConstr(edge_t[k][X[k][i]]<=(1-epsilon)*(edge_length[k]+0.2484908189));
			}
			model->addConstr(2*edge_t[1][9]+edge_t[1][12]+2*edge_t[1][4]+4*edge_t[1][13]==edge_length[1]);
			model->addConstr(edge_t[1][1]==edge_t[1][9]);
			model->addConstr(edge_t[1][8]==edge_t[1][4]);
			model->addConstr(edge_t[1][10]==edge_t[1][13]);
			model->addConstr(edge_t[1][2]==edge_t[1][13]);
			model->addConstr(edge_t[1][3]==edge_t[1][13]);
			// compatability constraints
			model->addConstr(2*edge_t[2][9]+edge_t[2][12]==edge_length[2]);
			model->addConstr(edge_t[2][1]==edge_t[2][9]);
			model->addConstr(2*edge_t[3][4]+4*edge_t[3][13]==edge_length[3]);
			model->addConstr(edge_t[3][8]==edge_t[3][4]);
			model->addConstr(edge_t[3][10]==edge_t[3][13]);
			model->addConstr(edge_t[3][2]==edge_t[3][13]);
			model->addConstr(edge_t[3][3]==edge_t[3][13]);
			model->addConstr(edge_t[4][15]+2*edge_t[4][11]+2*edge_t[4][5]+edge_t[4][14]+edge_t[4][16]==edge_length[4]);//+0.2484908189+edge_length[5]+edge_length[6]);
			model->addConstr(edge_t[4][11]==edge_t[4][7]);
			model->addConstr(edge_t[4][6]==edge_t[4][5]);
			model->addConstr(edge_t[5][15]==(edge_length[5]+0.2484908189/2.0)*edge_t[2][12]/edge_length[2]);
			model->addConstr(edge_t[5][7]==(edge_length[5]+0.2484908189/2.0)*edge_t[2][9]/edge_length[2]);
			model->addConstr(edge_t[5][11]==edge_t[5][7]);
			model->addConstr(edge_t[6][14]==(edge_length[6]+0.2484908189/2.0)*edge_t[2][12]/edge_length[2]);
			model->addConstr(edge_t[6][5]==(edge_length[6]+0.2484908189/2.0)*edge_t[2][9]/edge_length[2]);
			model->addConstr(edge_t[6][6]==edge_t[6][5]);
			if(theta!=-1){
				for(register unsigned int k=1; k<=n_edges; k++)
					for(register unsigned int i=1; i<=X_length[k]; i++)
						for(register unsigned int j=1; j<=X_length[k]; j++)
							if(i!=j) model->addConstr(y[X[k][i]]>=edge_t[k][X[k][i]]-edge_t[k][X[k][j]]);
				GRBLinExpr sum=0; for(register unsigned int i=1; i<=n; i++) sum+=y[i];
				model->addConstr(sum<=(1.0000001-theta)*total_length);
			}
			model->addConstr(t[1]==edge_t[1][1]+edge_t[2][1]); model->addConstr(t[2]==edge_t[1][2]+edge_t[3][2]);
			model->addConstr(t[3]==edge_t[1][3]+edge_t[3][3]); model->addConstr(t[4]==edge_t[1][4]+edge_t[3][4]);
			model->addConstr(t[5]==edge_t[4][5]+edge_t[6][5]); model->addConstr(t[6]==edge_t[4][6]+edge_t[6][6]);
			model->addConstr(t[7]==edge_t[4][7]+edge_t[5][7]); model->addConstr(t[8]==edge_t[1][8]+edge_t[3][8]);
			model->addConstr(t[9]==edge_t[1][9]+edge_t[2][9]); model->addConstr(t[10]==edge_t[1][10]+edge_t[3][10]);
			model->addConstr(t[11]==edge_t[4][11]+edge_t[5][11]); model->addConstr(t[12]==edge_t[1][12]+edge_t[2][12]);
			model->addConstr(t[13]==edge_t[1][13]+edge_t[3][13]); model->addConstr(t[14]==edge_t[4][14]+edge_t[6][14]);
			model->addConstr(t[15]==edge_t[4][15]+edge_t[5][15]); model->addConstr(t[16]==edge_t[4][16]);
			break;}
		case 3:{
			// define edge lengths
			edge_length[1]=2.690496525; edge_length[2]=0.9336668476; edge_length[3]=2.261143563; edge_length[4]=2.294528721; edge_length[5]=3.071743882; edge_length[6]=14.6132916; edge_length[7]=4.578479936; 
			edge_length[8]=4.831579876; edge_length[9]=8.491533777; edge_length[10]=10.75505626; edge_length[11]=0.6938112327; edge_length[12]=7.400705589;
			for(register unsigned int i=1; i<= n_edges; i++) if(i==remove_edge){edge_length[i]=0.000000001; break;}
			total_length=0.0; for(register unsigned int i=1; i<=n_edges; i++) total_length+=edge_length[i]; 
			// define subsets of taxa X[v]
			X_length[1]=3; X_length[2]=5; X_length[3]=6; X_length[4]=3; X_length[5]=5; X_length[6]=11; X_length[7]=13; X_length[8]=3; X_length[9]=5; X_length[10]=9; X_length[11]=3; X_length[12]=4;
			for(register unsigned int i=1; i<=n_edges; i++){X[i]=new int[X_length[i]+1]; gammaopt[i]=new double[X_length[i]+1];}
			for(register unsigned int k=1; k<=3; k++) for(register unsigned int i=1; i<=X_length[k]; i++) X[k][i]=i;
			for(register unsigned int k=4; k<=5; k++) for(register unsigned int i=1; i<=X_length[k]; i++) X[k][i]=6+i;
			for(register unsigned int k=6; k<=7; k++) for(register unsigned int i=1; i<=X_length[k]; i++) X[k][i]=i;
			for(register unsigned int k=8; k<=10; k++) for(register unsigned int i=1; i<=X_length[k]; i++) X[k][i]=13+i;
			for(register unsigned int k=11; k<=12; k++) for(register unsigned int i=1; i<=X_length[k]; i++) X[k][i]=18+i;
			// epsilon = 0 for the RDDP, epsilon = 1/2 for the R3DP
			if(epsilon!=-1){
				for(register unsigned int k=1; k<=n_edges; k++)
					for(register unsigned int i=1; i<=X_length[k]; i++) 
						model->addConstr(edge_t[k][X[k][i]]<=(1-epsilon)*edge_length[k]);
			}
			model->addConstr(2*edge_t[1][1]+edge_t[1][3]==edge_length[1]);
			model->addConstr(2*edge_t[2][1]+edge_t[2][3]+2*edge_t[2][4]==edge_length[2]);
			model->addConstr(2*edge_t[3][1]+edge_t[3][3]+2*edge_t[3][4]+edge_t[3][6]==edge_length[3]);
			model->addConstr(2*edge_t[4][7]+edge_t[4][9]==edge_length[4]);
			model->addConstr(2*edge_t[5][7]+edge_t[5][9]+2*edge_t[5][10]==edge_length[5]);
			model->addConstr(2*edge_t[6][1]+edge_t[6][3]+2*edge_t[6][4]+edge_t[6][6]+2*edge_t[6][7]+edge_t[6][9]+2*edge_t[6][10]==edge_length[6]);
			model->addConstr(2*edge_t[7][1]+edge_t[7][3]+2*edge_t[7][4]+edge_t[7][6]+2*edge_t[7][7]+edge_t[7][9]+2*edge_t[7][10]+2*edge_t[7][12]==edge_length[7]);
			model->addConstr(2*edge_t[8][14]+edge_t[8][16]==edge_length[8]);
			model->addConstr(2*edge_t[9][14]+edge_t[9][16]+2*edge_t[9][17]==edge_length[9]);
			model->addConstr(2*edge_t[10][14]+edge_t[10][16]+2*edge_t[10][17]+2*edge_t[10][19]+edge_t[10][21]+edge_t[10][22]==edge_length[10]);
			model->addConstr(2*edge_t[11][19]+edge_t[11][21]==edge_length[11]);
			model->addConstr(2*edge_t[12][19]+edge_t[12][21]+edge_t[12][22]==edge_length[12]);
			for(register unsigned int j=1; j<=n_edges; j++){
				model->addConstr(edge_t[j][1]==edge_t[j][2]);
				model->addConstr(edge_t[j][4]==edge_t[j][5]);
				model->addConstr(edge_t[j][7]==edge_t[j][8]);
				model->addConstr(edge_t[j][10]==edge_t[j][11]);
				model->addConstr(edge_t[j][12]==edge_t[j][13]);
				model->addConstr(edge_t[j][14]==edge_t[j][15]);
				model->addConstr(edge_t[j][17]==edge_t[j][18]);
				model->addConstr(edge_t[j][19]==edge_t[j][20]);
			}
			model->addConstr(edge_t[4][7]==edge_length[4]*edge_t[1][1]/edge_length[1]);
			model->addConstr(edge_t[4][9]==edge_length[4]*edge_t[1][3]/edge_length[1]);
			model->addConstr(edge_t[5][7]==edge_length[5]*edge_t[2][1]/edge_length[2]);
			model->addConstr(edge_t[5][9]==edge_length[5]*edge_t[2][3]/edge_length[2]);
			model->addConstr(edge_t[5][10]==edge_length[5]*edge_t[2][4]/edge_length[2]);
			model->addConstr(edge_t[8][14]==edge_length[8]*edge_t[1][1]/edge_length[1]);
			model->addConstr(edge_t[8][16]==edge_length[8]*edge_t[1][3]/edge_length[1]);
			model->addConstr(edge_t[9][14]==edge_length[9]*edge_t[2][1]/edge_length[2]);
			model->addConstr(edge_t[9][16]==edge_length[9]*edge_t[2][3]/edge_length[2]);
			model->addConstr(edge_t[9][17]==edge_length[9]*edge_t[2][4]/edge_length[2]);
			model->addConstr(edge_t[11][19]==edge_length[11]*edge_t[1][1]/edge_length[1]);
			model->addConstr(edge_t[11][21]==edge_length[11]*edge_t[1][3]/edge_length[1]);
			if(theta!=-1){
				for(register unsigned int k=1; k<=n_edges; k++)
					for(register unsigned int i=1; i<=X_length[k]; i++)
						for(register unsigned int j=1; j<=X_length[k]; j++)
							if(i!=j) model->addConstr(y[X[k][i]]>=edge_t[k][X[k][i]]-edge_t[k][X[k][j]]);
				GRBLinExpr sum=0; for(register unsigned int i=1; i<=n; i++) sum+=y[i];
				model->addConstr(sum<=(1.0000001-theta)*total_length);
			}
			model->addConstr(t[1]==edge_t[1][1]+edge_t[2][1]+edge_t[3][1]+edge_t[6][1]+edge_t[7][1]);
			model->addConstr(t[2]==t[1]);
			model->addConstr(t[3]==edge_t[1][3]+edge_t[2][3]+edge_t[3][3]+edge_t[6][3]+edge_t[7][3]);
			model->addConstr(t[4]==edge_t[2][4]+edge_t[3][4]+edge_t[6][4]+edge_t[7][4]);
			model->addConstr(t[5]==t[4]);
			model->addConstr(t[6]==edge_t[3][6]+edge_t[6][6]+edge_t[7][6]);
			model->addConstr(t[7]==edge_t[4][7]+edge_t[5][7]+edge_t[6][7]+edge_t[7][7]);
			model->addConstr(t[8]==t[7]);
			model->addConstr(t[9]==edge_t[4][9]+edge_t[5][9]+edge_t[6][9]+edge_t[7][9]);
			model->addConstr(t[10]==edge_t[5][10]+edge_t[6][10]+edge_t[7][10]);
			model->addConstr(t[11]==t[10]);
			model->addConstr(t[12]==edge_t[7][12]);
			model->addConstr(t[13]==t[12]);
			model->addConstr(t[14]==edge_t[8][14]+edge_t[9][14]+edge_t[10][14]);
			model->addConstr(t[15]==t[14]);
			model->addConstr(t[16]==edge_t[8][16]+edge_t[9][16]+edge_t[10][16]);
			model->addConstr(t[17]==edge_t[9][17]+edge_t[10][17]);
			model->addConstr(t[18]==t[17]);
			model->addConstr(t[19]==edge_t[10][19]+edge_t[11][19]+edge_t[12][19]);
			model->addConstr(t[20]==t[19]);
			model->addConstr(t[21]==edge_t[10][21]+edge_t[11][21]+edge_t[12][21]);
			model->addConstr(t[22]==edge_t[10][22]+edge_t[12][22]);
		}
	}
}

void updateGammaopt(){
	double tol=0.000001;
	switch(input_flag){
		case 1:{
			// allocation of edge 1
			for(register unsigned int i=1; i<=X_length[1]; i++){
  				if(edge_t[1][X[1][i]].get(GRB_DoubleAttr_X)-edge_t[2][X[1][i]].get(GRB_DoubleAttr_X)<tol) gammaopt[1][i]=0;
  				else gammaopt[1][i]=(edge_t[1][X[1][i]].get(GRB_DoubleAttr_X)-edge_t[2][X[1][i]].get(GRB_DoubleAttr_X))/edge_length[1];}
			for(register unsigned int k=2; k<=4; k++){
				// allocation of edge k
				for(register unsigned int i=1; i<=X_length[k]; i++){
					if(edge_t[k][X[k][i]].get(GRB_DoubleAttr_X)<tol) gammaopt[k][i]=0;
					else if(k==2) gammaopt[k][i]=edge_t[k][X[k][i]].get(GRB_DoubleAttr_X)/edge_length[k];
					else gammaopt[k][i]=edge_t[k][X[k][i]].get(GRB_DoubleAttr_X)/(edge_length[k]+2.283285348/2.0);}}
		break;}
		case 2:{
			for(register unsigned int k=1; k<=n_edges; k++)
				for(register unsigned int i=1; i<=X_length[k]; i++){
					if(edge_t[k][X[k][i]].get(GRB_DoubleAttr_X)<tol) gammaopt[k][i]=0;
					else{
						if(k>=5){
							if(X[k][i]>=14) gammaopt[k][i]=edge_t[k][X[k][i]].get(GRB_DoubleAttr_X)/(edge_length[k]+0.2484908189/2.0);
							else gammaopt[k][i]=edge_t[k][X[k][i]].get(GRB_DoubleAttr_X)/(edge_length[k]+0.2484908189/2.0);
						} else
						gammaopt[k][i]=edge_t[k][X[k][i]].get(GRB_DoubleAttr_X)/edge_length[k];}}
		break;}
		case 3:{
			for(register unsigned int k=1; k<=n_edges; k++)
				for(register unsigned int i=1; i<=X_length[k]; i++){
					if(edge_t[k][X[k][i]].get(GRB_DoubleAttr_X)<tol) gammaopt[k][i]=0;
					else gammaopt[k][i]=edge_t[k][X[k][i]].get(GRB_DoubleAttr_X)/edge_length[k];}
		break;}
	}
}

void calculateTheta(){
	double* delta=new double[n+1];
	switch(input_flag){
		case 1:{
			for(register unsigned int k=1; k<=n_edges; k++){ // consider all edges (u,v) in E_var
				for(register unsigned int l=1; l<=X_length[k]; l++){ // consider all taxa x_i in X[v]
					if(k==2) delta[X[k][l]]=delta[X[k-1][l+1]]; else delta[X[k][l]]=0.0; // take the maximum delta_i so far
					for(register unsigned int j=1; j<=X_length[k]; j++){ // consider all taxa y in X[v]\{x_i}
						if(j!=l && edge_length[k]*(gammaopt[k][l]-gammaopt[k][j])>delta[X[k][l]]) 
							delta[X[k][l]]=edge_length[k]*(gammaopt[k][l]-gammaopt[k][j]);
					}
				}
			}
		break;}
		case 2:{
			for(register unsigned int k=1; k<=n_edges; k++)
				for(register unsigned int l=1; l<=X_length[k]; l++){
					if(k==1 || k==4) delta[X[k][l]]=0.0;
					if(k==2 || k==5) delta[X[k][l]]=delta[X[k-1][l]];
					if(k==3 || k==6) delta[X[k][l]]=delta[X[k-2][l+3]];
					for(register unsigned int j=1; j<=X_length[k]; j++){
						if(j!=l && edge_length[k]*(gammaopt[k][l]-gammaopt[k][j])>delta[X[k][l]]) 
							delta[X[k][l]]=edge_length[k]*(gammaopt[k][l]-gammaopt[k][j]);
					}
				}
		break;}
		case 3:{
			for(register unsigned int k=1; k<=n_edges; k++)
				for(register unsigned int l=1; l<=X_length[k]; l++){
					if(k==1 || k==4 || k==8) delta[X[k][l]]=0.0;
					if((k==2 || k==5 || k==9 || k==12) && l>=4) delta[X[k][l]]=0.0; if((k==2 || k==5 || k==9 || k==12) && l<=3) delta[X[k][l]]=delta[X[k-1][l]];
					if(k==3 && l==6) delta[X[k][l]]=0.0; if(k==3 && l<=5) delta[X[k][l]]=delta[X[k-1][l]];
					if(k==6 && l>=7) delta[X[k][l]]=delta[X[k-1][l-6]]; if(k==6 && l<=6) delta[X[k][l]]=delta[X[k-3][l]];
					if(k==7 && l>=12) delta[X[k][l]]=0.0; if(k==7 && l<=11) delta[X[k][l]]=delta[X[k-1][l]];
					if(k==10 && l>=6) delta[X[k][l]]=0.0; if(k==10 && l<=5) delta[X[k][l]]=delta[X[k-1][l]];
					if(k==11) delta[X[k][l]]=delta[X[k-1][5+l]];
					for(register unsigned int j=1; j<=X_length[k]; j++){
						if(j!=l && edge_length[k]*(gammaopt[k][l]-gammaopt[k][j])>delta[X[k][l]]) 
							delta[X[k][l]]=edge_length[k]*(gammaopt[k][l]-gammaopt[k][j]);
					}
				}
		break;}
	}
	double sum=0.0; for(register unsigned int i=1; i<=n; i++) sum+=delta[i];
	theta = 1-sum/total_length;
	delete [] delta;
}

void setModel(){
	model = new GRBModel(*env);
    // setup model variables
    y = new GRBVar[n+1];
    t = new GRBVar[n+1];
    edge_t = new GRBVar*[n+1];
    for(int i=1; i<=n; i++){
    	string name="aux_"+to_string(i);
    	y[i] = model->addVar(0.0, GRB_INFINITY, 0.0, GRB_CONTINUOUS, name);
    	name="t_"+to_string(i);
    	t[i] = model->addVar(0.0, GRB_INFINITY, 0.0, GRB_CONTINUOUS, name);
    	edge_t[i] = new GRBVar[n+1];
    	for(int j=1; j<=n; j++){
    		name="edge_t_"+to_string(i)+","+to_string(j);
    		edge_t[i][j] = model->addVar(0.0, GRB_INFINITY, 0.0, GRB_CONTINUOUS, name);
    	}
    }
  	// setup model constraints
    setConstraints();
}

int choose(int N, int K){if(K==0) return 1; return (N*choose(N-1,K-1))/K;}

// calculate all subsets of {1..N} of size k in cyclic order
void calculateY(){
    string bitmask(k, 1); bitmask.resize(n, 0);
 	int counter=0;
    do {
    	Y[++counter] = new int[k+1]; int j=1;
    	for(register unsigned int i=1; i<=n; i++) 
    		if(bitmask[cyclic[i]-1]) Y[counter][j++] = cyclic[i];
    } while (prev_permutation(bitmask.begin(), bitmask.end()));
}

void solveOrderk(){
	Yopt=new int*[7]; for(register unsigned int i=1; i<=6; i++) Yopt[i]=new int[k+1];
	// consider all (n choose k) subsets Y of X in cyclic order
	n_Y = choose(n,k); Y = new int*[n_Y+1]; calculateY();
	int counter=1; double rdd=-1, fdd=-1, edd=-1, mcd=-1, fid=-1, eid=-1, tol=0.0000001;
	double pd_rdd,pd_fdd,pd_edd;
	do{
		// calculate PD(Y)
		double f=0.0; int last_taxon=n+1;
		for(register unsigned int i=1; i<=k; i++){f+=dist[last_taxon][Y[counter][i]]; last_taxon=Y[counter][i];}
		f+=dist[last_taxon][n+1]; f/=2.0; //cout << "PD(Y) = " << f << endl;
  		// calculate ID^max(Y)
    	GRBQuadExpr obj=0; for(register unsigned int i=1; i<=k; i++) obj+=(t[Y[counter][i]]);
    	if(theta!=-1){
    		GRBLinExpr sum=0; for(register unsigned int i=1; i<=n; i++) sum+=y[i];
    		model->setObjective(obj-tol*sum, GRB_MAXIMIZE);
    	} else model->setObjective(obj, GRB_MAXIMIZE);
  		model->set("LogToConsole","0");
  		model->optimize();
  		updateGammaopt();
    	double g=0.0, g_ES=0.0, g_FP=0.0;
  		for(register unsigned int i=1; i<=k; i++){
  			g+=LB[Y[counter][i]]+t[Y[counter][i]].get(GRB_DoubleAttr_X);
  			g_ES+=s_ES[Y[counter][i]];
  			g_FP+=s_FP[Y[counter][i]];
  		} //cout << "ID^max(Y) = " << g << endl;
  		if(epsilon!=-1){
  			if(f-g>rdd){ if(f-g>tol) rdd = f-g; else rdd=0;
  				for(register unsigned int i=1; i<=k; i++) Yopt[1][i]=Y[counter][i]; pd_rdd=f; 
  			}
  			if(f-g_FP>fdd){ if(f-g_FP>tol) fdd = f-g_FP; else fdd=0;
  				for(register unsigned int i=1; i<=k; i++) Yopt[2][i]=Y[counter][i]; pd_fdd=f; 
  			}
  			if(f-g_ES>edd){ if(f-g_ES>tol) edd = f-g_ES; else edd=0;
  				for(register unsigned int i=1; i<=k; i++) Yopt[3][i]=Y[counter][i]; pd_edd=f;
  			}
  		}
  		if(theta!=-1){
  			if(g>mcd){ mcd = g;
  				for(register unsigned int i=1; i<=k; i++) Yopt[4][i]=Y[counter][i];
			}
  			if(g_FP>fid){ fid = g_FP;
  				for(register unsigned int i=1; i<=k; i++) Yopt[5][i]=Y[counter][i];
  			}
  			if(g_ES>eid){ eid = g_ES;
  				for(register unsigned int i=1; i<=k; i++) Yopt[6][i]=Y[counter][i];
  			}
  		}
  	}while(++counter<=n_Y);
  	cout << "optimal allocation:" << endl;
  	for(register unsigned int k=1; k<=n_edges; k++){
		for(register unsigned int i=1; i<=X_length[k]; i++){
			cout << "gamma("<<X[k][i]<<","<<"e_"<<k<<")= \t" << gammaopt[k][i] << "\n"; }cout << endl;}
	cout << endl;
	if(theta!=-1){
  		cout << "MCD("<<k<<","<<theta<<") = "<< mcd << ";\t Y_C = { "; for(register unsigned int i=1; i<=k; i++) cout << Yopt[4][i] << " "; cout << "}" << endl;
		cout << "FID("<<k<<") = " << fid << ";\t Y_F = { "; for(register unsigned int i=1; i<=k; i++) cout << Yopt[5][i] << " "; cout << "}" << endl;
  		cout << "EID("<<k<<") = " << eid << ";\t Y_E = { "; for(register unsigned int i=1; i<=k; i++) cout << Yopt[6][i] << " "; cout << "}" << endl;	
		/* calculate the corresponding ranking
		double* t_score = new double[k+1]; for(register unsigned int i=1; i<=k; i++) t_score[i]=LB[Yopt[4][i]]+t[Yopt[4][i]].get(GRB_DoubleAttr_X);
  		int* ranking=new int[k+1];
  		for(register unsigned int h=1; h<=k; h++){
  			double max=-1; int max_idx=-1;
  			for(register unsigned int i=1; i<=k; i++)
  				if(max<t_score[i]){max=t_score[i]; max_idx=i;}
  			t_score[max_idx]=-1;
  			ranking[h]=Yopt[4][max_idx];
  		}
  		for(register unsigned int h=1; h<=k; h++) cout << ranking[h] << " | " << LB[ranking[h]]+t[ranking[h]].get(GRB_DoubleAttr_X)<<endl; //<< Yopt[1][h] << ": " << t[Yopt[1][h]].get(GRB_DoubleAttr_X) << endl;
  		delete [] t_score; delete [] ranking; */
	}
	if(epsilon!=-1){
		cout << "RDD("<<k<<","<<epsilon; if(theta!=-1) cout << ","<<theta;
  		cout <<") = "<< rdd << ";\t Y_R = { "; for(register unsigned int i=1; i<=k; i++) cout << Yopt[1][i] << " "; cout << "}\t normalized PD score = "<< pd_rdd/k << endl;
		cout << "FDD("<<k<<") = " << fdd << ";\t Y_F = { "; for(register unsigned int i=1; i<=k; i++) cout << Yopt[2][i] << " "; cout << "}\t normalized PD score = "<< pd_fdd/k << endl;
  		cout << "EDD("<<k<<") = " << edd << ";\t Y_E = { "; for(register unsigned int i=1; i<=k; i++) cout << Yopt[3][i] << " "; cout << "}\t normalized PD score = "<< pd_edd/k << endl;
  		if(theta==-1){calculateTheta(); cout<<"theta_R = "<<theta<<endl; theta=-1;}
  		/* calculate the corresponding ranking
  		double* t_score = new double[k+1]; for(register unsigned int i=1; i<=k; i++) t_score[i]=t[Yopt[1][i]].get(GRB_DoubleAttr_X);
  		int* ranking=new int[k+1];
  		for(register unsigned int h=1; h<=k; h++){
  			double max=-1; int max_idx=-1;
  			for(register unsigned int i=1; i<=k; i++)
  				if(max<t_score[i]){max=t_score[i]; max_idx=i;}
  			t_score[max_idx]=-1;
  			ranking[h]=Yopt[1][max_idx];
  		}
  		for(register unsigned int h=1; h<=k; h++) cout << ranking[h] << " | " << t[ranking[h]].get(GRB_DoubleAttr_X)<<endl; //<< Yopt[1][h] << ": " << t[Yopt[1][h]].get(GRB_DoubleAttr_X) << endl;
  		delete [] t_score; delete [] ranking; */
  	}
  	cout <<"theta_ES = "<<theta_ES<<endl<<endl;
}

void calculateES(){
	s_ES = new double[n+1];
	switch(input_flag){
		case 1:{
			s_ES[1]=2.550976538325; s_ES[2]=3.615782360615; s_ES[3]=3.94522669565; s_ES[4]=2.0153801856; s_ES[5]=3.3304778729;
			s_ES[6]=2.550976538325; s_ES[7]=1.2156493833; s_ES[8]=3.98193634345; s_ES[9]=3.615782360615; s_ES[10]=1.2156493833; 
			// compatability: find theta such that
			// 4.853363685*(0.5-0.125)+4.853363685*(0.25-0.125)+0.1989380193*(0.5-0.25)+0.1255187229*(0.5-0.25)<=(1-theta)*(4.853363685+0.2035135321+0.1255187229+0.1989380193)
			// equivalently: 2.50779602805 <= (1-theta)*5.3813339593
			theta_ES=0.533982; break;}
		case 2:{
			s_ES[9]=0.819217895285; s_ES[1]=s_ES[9]; s_ES[12]=1.61125406874; s_ES[4]=2.044292814475; s_ES[8]=s_ES[4];
			s_ES[13]=1.4107502712624997; s_ES[10]=s_ES[13]; s_ES[2]=1.6594103692125; s_ES[3]=s_ES[2];
			s_ES[15]=2.34743354248875; s_ES[7]=1.243778189444375; s_ES[11]=s_ES[7]; s_ES[5]=1.149872036994375; s_ES[6]=s_ES[5];
			s_ES[14]=2.07687288508875; s_ES[16]=3.561867330055; 
			// compatability: find theta such that
			// 4*0.8029194702*(0.125-0.0625)+2.737294992*(0.5-0.25)+2.025795591*(0.5-0.25)+2.566916906*(0.5-0.25)+0.04044767411*(0.5-0.0625)
			// <=(1-theta)*(2.737294992+0.1891780108+0.8029194702+2.025795591+2.566916906+0.04044767411)
			// equivalently: 2.050927597223125<=(1-theta)*8.36255264411
			theta_ES=0.7547486174968769; break;}
		case 3:{
			s_ES[1]=2.2369816431375; s_ES[2]=s_ES[1]; s_ES[3]=3.858520262175; s_ES[4]=4.440363553775; s_ES[5]=s_ES[4]; s_ES[6]=9.9211721655;
			s_ES[7]=3.1535415968; s_ES[8]=s_ES[7]; s_ES[9]=5.48785523; s_ES[10]=5.3596678705; s_ES[11]=s_ES[10]; s_ES[12]=13.98052943; s_ES[13]=s_ES[12];
			s_ES[14]=4.675265772475; s_ES[15]=s_ES[14]; s_ES[16]=7.82276809175; s_ES[17]=7.20838293465; s_ES[18]=s_ES[17];
			s_ES[19]=7.01652424055; s_ES[20]=s_ES[19]; s_ES[21]=10.7097735541; s_ES[22]=14.2512376005; 
			// compatability: find theta such that
			// 2.690496525*(0.5-0.25)+2*14.6132916*(0.0625-0.03125)+14.6132916*(0.25-0.03125)+2*14.6132916*(0.0625-0.03125)+3*14.6132916*(0.125-0.03125)+2*4.578479936*(0.25-0.015625)
			// +4.831579876*(0.5-0.25)+8.491533777*(0.25-0.125)+7.400705589*(0.25-0.125)+7.400705589*(0.5-0.125)
			// <=(1-theta)*(2.690496525+0.9336668476+2.261143563+2.294528721+3.071743882+14.6132916+4.578479936+0.6938112327+7.400705589+4.831579876+8.491533777+10.75505626)
			// equivalently: 17.921783336875<=(1-theta)*62.6160378093
			theta_ES=0.7137828587708375; break;}
	}
}

void calculateFP(){
	s_FP = new double[n+1];
	switch(input_flag){
		case 1:{
			s_FP[1]=2.6626915961; s_FP[2]=3.72137914369; s_FP[3]=3.7217965801; s_FP[4]=1.9814612635833333; s_FP[5]=2.11713695165;
			s_FP[6]=2.6626915961; s_FP[7]=1.8392793049333334; s_FP[8]=3.7707427773; s_FP[9]=3.72137914369; s_FP[10]=1.8392793049333334; break;}
		case 2:{
			s_FP[9]=1.0361741519766665; s_FP[1]=s_FP[9]; s_FP[12]=1.0435216436566666; s_FP[4]=2.0173763209333333; s_FP[8]=s_FP[4];
			s_FP[13]=1.4576634959583332; s_FP[10]=s_FP[13]; s_FP[2]=1.7063235939083334; s_FP[3]=s_FP[2];
			s_FP[15]=1.9898156556419049; s_FP[7]=1.4261985323419046; s_FP[11]=s_FP[7]; s_FP[5]=1.3773858228085714; s_FP[6]=s_FP[5];
			s_FP[14]=1.6290681124085713; s_FP[16]=3.5474217321585715; break;}
		case 3:{
			s_FP[1]=3.9192181956231464; s_FP[2]=s_FP[1]; s_FP[3]=4.081898743273147; s_FP[4]=5.112158122373147; s_FP[5]=s_FP[4]; s_FP[6]=6.622496571353147;
			s_FP[7]=4.199396710553146; s_FP[8]=s_FP[7]; s_FP[9]=4.519701955253146; s_FP[10]=4.773936049253146; s_FP[11]=s_FP[10];
			s_FP[12]=13.188100210307693; s_FP[13]=s_FP[12]; s_FP[14]=6.237577696944444; s_FP[15]=s_FP[14]; s_FP[16]=6.443552308844444;
			s_FP[17]=6.634430464411111; s_FP[18]=s_FP[17]; s_FP[19]=8.522245276761112; s_FP[20]=s_FP[19]; s_FP[21]=10.444762567261112;
			s_FP[22]=10.907303389361111; break;}
	}
}

void deallocate(){
	for(register unsigned int i=1; i<=n+1; i++) delete [] dist[i]; delete [] dist;
	delete [] cyclic;
	delete [] LB; 
	for(register unsigned int i=1; i<=n_Y; i++) delete [] Y[i]; delete [] Y; 
	for(register unsigned int i=1; i<=n; i++) delete [] edge_t[i]; delete [] edge_t;
	delete [] t; delete [] y; delete model; delete env;
	delete [] s_ES; delete [] s_FP;
	for(register unsigned int i=1; i<=n_edges; i++){delete [] X[i]; delete [] gammaopt[i];}
	delete [] X; delete [] gammaopt; delete [] edge_length; delete [] X_length;
	for(register unsigned int i=1; i<=6; i++) delete [] Yopt[i]; delete [] Yopt;
}

/* Assumptions: argv[1] is the number of taxa
				argv[2] is the order epsilon
				argv[3] is the order theta
				argv[4] is the flag for hardcoded constraints
				argv[5] is the distance matrix
				(optional) argv[6] is the order kappa of the RDDP. Otherwise, all orders of the RDDP are considered. 
				(optional) argv[7] is the index of edge e to obtain T\e */
/* Coded calls:
	solver 10 epsilon theta 1 simTreeDist10.txt (kappa remove_edge)
	solver 16 epsilon theta 2 simTreeDist16.txt (kappa remove_edge)
	solver 22 epsilon theta 3 albatrosDist22.txt (kappa remove_edge)

	for example: the call 

	' solver 10 -1 0.8 1 simTreeDist10.txt 5 '

	solves the MCDP of order (5,0.8) for the Yule tree on 10 taxa, or the call

	' solver 16 0 -1 2 simTreeDist16.txt '

	solve the RDDP for all orders kappa for the Yule tree on 16 taxa.
*/
int main (int argc, char * const argv[]){
	// read inputs
	n=atoi(argv[1]);
	epsilon=atof(argv[2]);
	try{if(epsilon>0.5) throw invalid_argument("There are no feasible solution for epsilon > 0.5!");}catch(invalid_argument& e){cerr << e.what() << endl; return -1;}
	try{if(epsilon<0 && epsilon!=-1) throw invalid_argument("There are no feasible solution for epsilon < 0!");}catch(invalid_argument& e){cerr << e.what() << endl; return -1;}
	theta=atof(argv[3]);
	try{if((theta<0 || theta>1) && theta!=-1) throw invalid_argument("There are no feasible solution for values of theta outside [0,1]!");}catch(invalid_argument& e){cerr << e.what() << endl; return -1;}
	input_flag=atoi(argv[4]);
	switch(input_flag){
		case 1:{n_edges=4; break;}
		case 2:{n_edges=6; break;}
		case 3:{n_edges=12; break;}}
	if(argv[6]==NULL || atoi(argv[6])==-1){
		k=-1;
	} else {
		int l=atoi(argv[6]);
		try{if(l<2) throw invalid_argument("k >= 2 is required!");}catch(invalid_argument& e){cerr << e.what() << endl; return -1;}
		try{if(l>n) throw invalid_argument("The order of the RDDP exceeds the number of taxa!");}catch(invalid_argument& e){cerr << e.what() << endl; return -1;}
		k=l;
	}
	if(argv[7]==NULL || atoi(argv[7])==-1){
		remove_edge=-1;
	} else remove_edge=atoi(argv[7]);
	ReadDistanceMatrix(argv[5]);
	setBounds();
	calculateES();
	calculateFP();
	env = new GRBEnv(true); env->set("LogFile", "PDdif.log"); env->start();
	setModel();
	cout << endl << "n = "<< n<<" taxa."<< endl << endl;
	if(k!=-1) solveOrderk(); 
	else for(k=2;k<=n;k++){
		auto start = chrono::system_clock::now();
		solveOrderk();
		auto end = chrono::system_clock::now();
		double elapsed_seconds = chrono::duration_cast<chrono::duration<double>>(end - start).count();
		cout << "run time = " << elapsed_seconds << " seconds." << endl << endl;
	}
    deallocate();
	return 0;	
}

