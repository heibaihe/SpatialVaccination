/** **************************************************************************************************** **/ 
/** **************************************************************************************************** **/
/** **************************************************************************************************** **/
/** **************************************************************************************************** **/
/** **************************************************************************************************** **/
/** **************************************************************************************************** **/
/** **************************************************************************************************** **/
/** **************************************************************************************************** **/
/** **************************************************************************************************** **/
/** **************************************************************************************************** **/

#include "math.h"
#include "stdio.h"
#include "stdlib.h"
#include "time.h"

//Fixed parameters:
#define N 7800000000 // global population  
#define Mmax 30 // threshold on number of mutants to identify take over 
#define T 913  // maximal simulation time
#define Realizations 5000 // number of realizations for probability computation
#define r 1 // recovery rate - we normalize time such that an infection cycle of 4 days takes 1 time unit
#define dt 0.01 // time step for the simulation, in time units of infection cycle
#define Vmax 1.0 // vaccination rate (population fraction per year)
#define H 0.1 // permitted infection rate (population fraction per year)
#define beta 4 // infection rate of wild type
#define d 1 // fitness deficiency for mutants
#define e 1 // escape capacity for mutants
#define K 10 // number of regions
#define c 0.01 // contact ratio between regions

//parameters to be computed later (double precision)
double v; // vaccination rate per infection cycle (=Vmax*4/365)
double h; // permitted infection rate per infection cycle  (=H*4/365)
double betam; // infection rate for mutants (=d*beta)
double NK; // population per region (=N/K)
double mu; // mutation rate (computed in loop)
double factor;  // step for mu in computation (=0.1 orders of magnitude)
double wane; // waning rate

// SIR variables for each region and their summations:
double S[K],Sdot[K],I[K],Idot[K],R[K],Rdot[K],VS[K],VSdot[K],VR[K],VRdot[K],Im[K],Ihat[K],Imhat[K],sumS,sumI,sumR,sumVS,sumVR,sumM,wanek[K],waneRk[K];
double S2[K],Sdot2[K],I2[K],Idot2[K],R2[K],Rdot2[K],VS2[K],VSdot2[K],VR2[K],VRdot2[K];
double lk; //lockdown coefficient in currently computed region
// poisson process for mutants takes rates and produces number of successes:
double rateMut[K],rateInf[K],rateRec[K],nMut[K],nInf[K],nRec[K];

double t;  // time (computed in loop)
double control; // vaccination phase (=-1 before vaccination starts, =1 during vaccination phase) 
double vK[K]; // vaccination rate in each region
 
int i,k; // region index in computation loops
int kk; // region being currently vaccinated
int jj; // index for mutation rate loop

double count1; // realization number
double judge,judge2; // tests if mutant took over (1=yes, -1=no)
double count2; // in how many realizations the mutant took over 
double countT; // measure the duration of each vaccination period

// define poisson function that takes arrival rate Lambda and returns the number of successes
double possion(double Lambda)
{
	double  result = 0;
	long double u;
	long double p = 1.0;
	long double l = exp(-Lambda);
        
	while(p>=l)
	{
		u=rand()/(1.0+RAND_MAX);;
		p *= u;
		result++;
	}
	return result-1;
}


/** **************************************************************************************************** **/
//      The simulation for one realization
/** **************************************************************************************************** **/

double model()
{

// initializing SIR variables 

	for(k=0;k<K;k++)
	{
		S[k]=1-h;
		Sdot[k]=0;
		I[k]=h;
		Idot[k]=0;
		R[k]=0;
		Rdot[k]=0;
		VS[k]=0;
		VSdot[k]=0;
		VR[k]=0;
		VRdot[k]=0;
		Im[k]=0;
		vK[k]=0; // in the year before vaccination all vaccination rates are 0
		
		S2[k]=0;
		Sdot2[k]=0;
		I2[k]=0;
		Idot2[k]=0;
		R2[k]=0;
		Rdot2[k]=0;
		VS2[k]=0;
		VSdot2[k]=0;
		VR2[k]=0;
		VRdot2[k]=0;
	}

	kk=0; // first region to be vaccinated
judge=-1;
	control=-1;
	countT=0;
	
	
// time loop 	

for(t=0;t<T;t=t+dt)
	{
		// test if we are already in the vaccination phase (second year)
		if((t>365/4.0-pow(10,-8))&&(t<365/4.0+pow(10,-8)))
		{
			control=1;
			vK[kk]=v*K;
			
			S2[kk]=S[kk];
			S[kk]=0;
			I2[kk]=I[kk];
			I[kk]=0;
			R2[kk]=R[kk];
			R[kk]=0;
			VS2[kk]=VS[kk];
			VS[kk]=0;
			VR2[kk]=VR[kk];
			VR[kk]=0;
		}
		if(control>0)
		{
		countT=countT+dt;}
		
		//calculate the effective infection pools for each region 
		for(k=0;k<K;k++)
		{
			if (K==1)
{
	Ihat[k]=I[k]+I2[k];
				Imhat[k]=Im[k];
}
if (K>1)
{
				Ihat[k]=(1-c)*(I[k]+I2[k]);
		    	Imhat[k]=(1-c)*Im[k];
				for(i=0;i<K;i++)
				{
					if(i!=k)
					{
						Ihat[k]=Ihat[k]+c*(I[i]+I2[i])/(K-1);
						Imhat[k]=Imhat[k]+c*Im[i]/(K-1);
					}
				}
			}
		// set waning rate for each region  
		wanek[k]=wane*v;
		waneRk[k]=wane*v;
				
		}
		
		// time-step updating of SIR variables for each region k 

		for(k=0;k<K;k++)
		
{
			// calculate region k¡¯s lockdown factor
if((S[k]+S2[k]>1/NK)&&(Ihat[k]>1/NK))  // verify that region k still has infections - otherwise the lockdown factor is 1
    			{
				lk=h/((1-mu)*beta*(S[k]+S2[k])*Ihat[k]);
    				if(lk>1)
    				{
    					lk=1;
				}
			}
			else 
			{
				lk=1;
			}
			
			// update derivatives of wild-type SIR variables
            // vaccination happens only for the variables of the second arrays to avoud repetitive vaccination  
			
			Sdot[k]=-(1-mu)*lk*beta*Ihat[k]*S[k]+wanek[k]*VS[k]+waneRk[k]*R[k];
    		Idot[k]=(1-mu)*lk*beta*Ihat[k]*S[k]-r*I[k];
    		Rdot[k]=r*I[k]+wanek[k]*VR[k]-waneRk[k]*R[k]+wanek[k]*VR[k];
    		VSdot[k]=vK[k]*(S2[k]+VS2[k])/(S2[k]+R2[k]+VS2[k]+VR2[k])-wanek[k]*VS[k]+waneRk[k]*VR[k];
    		VRdot[k]=vK[k]*(R2[k]+VR2[k])/(S2[k]+R2[k]+VS2[k]+VR2[k])-wanek[k]*VR[k]-waneRk[k]*VR[k];
    		
    		
    		Sdot2[k]=-(1-mu)*lk*beta*Ihat[k]*S2[k]-vK[k]*S2[k]/(S2[k]+R2[k]+VS2[k]+VR2[k])+wanek[k]*VS2[k]+waneRk[k]*R2[k];
    		Idot2[k]=(1-mu)*lk*beta*Ihat[k]*S2[k]-r*I2[k];
    		Rdot2[k]=r*I2[k]-vK[k]*R2[k]/(S2[k]+R2[k]+VS2[k]+VR2[k])+wanek[k]*VR2[k]-waneRk[k]*R2[k];
    		VSdot2[k]=-vK[k]*VS2[k]/(S2[k]+R2[k]+VS2[k]+VR2[k])-wanek[k]*VS2[k]+waneRk[k]*VR2[k];
    		VRdot2[k]=-vK[k]*VR2[k]/(S2[k]+R2[k]+VS2[k]+VR2[k])-waneRk[k]*VR2[k]-wanek[k]*VR2[k];
    				
    		if(S2[k]+R2[k]+VS2[k]+VR2[k]<1/NK)  // if all population are vaccinated:
			{
    			VSdot[k]=-wanek[k]*VS[k];
    			VRdot[k]=wanek[k]*VR[k];
    			Sdot2[k]=-(1-mu)*lk*beta*Ihat[k]*S2[k]+wanek[k]*VS2[k]+waneRk[k]*R2[k];
    			Rdot2[k]=r*I2[k]+wanek[k]*VR2[k]-waneRk[k]*R2[k];
    		    VSdot2[k]=-wanek[k]*VS2[k];
    		    VRdot2[k]=-waneRk[k]*VR2[k];
			}
		
			// update number of mutants

// arrival rates
			rateMut[k]=dt*mu*lk*beta*Ihat[k]*(S[k]+S2[k])*NK;
    		rateInf[k]=dt*lk*betam*(VS[k]+S[k]+VS2[k]+S2[k])*Imhat[k];
    		rateRec[k]=dt*r*Imhat[k];
			// call poisson function to compute number of respective events		
    			nMut[k]=possion(rateMut[k]);    				
    			nInf[k]=possion(rateInf[k]);
    			nRec[k]=possion(rateRec[k]);
			// update number of mutants
			Im[k]=Im[k]+nMut[k]+nInf[k]-nRec[k];
			if(Im[k]<0)
			{
				Im[k]=0;
			}
        
     			 // update wild-type SIR variables 

			S[k]=S[k]+Sdot[k]*dt;
			I[k]=I[k]+Idot[k]*dt;
			R[k]=R[k]+Rdot[k]*dt;
			VS[k]=VS[k]+VSdot[k]*dt;
			VR[k]=VR[k]+VRdot[k]*dt;
			
			S2[k]=S2[k]+Sdot2[k]*dt;
			I2[k]=I2[k]+Idot2[k]*dt;
			R2[k]=R2[k]+Rdot2[k]*dt;
			VS2[k]=VS2[k]+VSdot2[k]*dt;
			VR2[k]=VR2[k]+VRdot2[k]*dt;
			// make sure they are in the range of 0 and 1	
			if(S[k]<0)
			{
				S[k]=0;
			}
			if(I[k]<0)
			{
				I[k]=0;
			}
			if(R[k]<0)
			{
				R[k]=0;
			}
			if(VS[k]<0)
			{
				VS[k]=0;
			}
			if(VR[k]<0)
			{
				VR[k]=0;
			}
			if(S[k]>1)
			{
				S[k]=1;
			}
			if(I[k]>1)
			{
				I[k]=1;
			}
			if(R[k]>1)
			{
				R[k]=1;
			}
			if(VS[k]>1)
			{
				VS[k]=1;
			}
			if(VR[k]>1)
			{
				VR[k]=1;
			}
			
			if(S2[k]<0)
			{
				S2[k]=0;
			}
			if(I2[k]<0)
			{
				I2[k]=0;
			}
			if(R2[k]<0)
			{
				R2[k]=0;
			}
			if(VS2[k]<0)
			{
				VS2[k]=0;
			}
			if(VR2[k]<0)
			{
				VR2[k]=0;
			}
			
			if(S2[k]>1)
			{
				S2[k]=1;
			}
			if(I2[k]>1)
			{
				I2[k]=1;
			}
			if(R2[k]>1)
			{
				R2[k]=1;
			}
			if(VS2[k]>1)
			{
				VS2[k]=1;
			}
			if(VR2[k]>1)
			{
				VR2[k]=1;
			}
								
		}  // end of loop for updating of SIR variables for each region k 
		
		// judge if vaccination in region kk has reached the upper level of Vmax - if yes we move to the next region	
		if(kk<K)
		{	
	    	if((countT>(365/4.0)/K)&&(control>0))			
			{
				vK[kk]=0;
				kk=kk+1;
				if(kk==K)
				{
					kk=0;
				}
				if(kk<K) 
				{
					vK[kk]=v*K;
				}
				countT=0;
				
				// move the variables to the second arrays to avoud repetitive vaccination 
				S2[kk]=S[kk];
				S[kk]=0;
				I2[kk]=I[kk];
				I[kk]=0;
				R2[kk]=R[kk];
				R[kk]=0;
				VS2[kk]=VS[kk];
				VS[kk]=0;
				VR2[kk]=VR[kk];
				VR[kk]=0;
				
			}
		}
		
		// summing the SIR variables over all regions 
		sumS=0;
		sumI=0;
		sumR=0;
		sumVS=0;
		sumVR=0;
		sumM=0;
    		for(k=0;k<K;k++)
   			{
    		sumS=sumS+S[k]/K+S2[k]/K;
    		sumI=sumI+I[k]/K+I2[k]/K;
    		sumR=sumR+R[k]/K+R2[k]/K;
    		sumVS=sumVS+VS[k]/K+VS2[k]/K;
    		sumVR=sumVR+VR[k]/K+VR2[k]/K;
    		sumM=sumM+Im[k];
			}   	
		
		// Finish iterating time (i.e, end the computation of the current realization) if either
// (1) there are no infection nor mutants, or (2) the number of mutants is higher than the takeover threshold
// otherwise advance time and repeat the process 	
		if((sumI<1/(double)N)&&(sumM<1))  // no infections
 		{  
    			t=T+1;	// end process by making time above the maximum bound 	
		}
		else if(sumM>Mmax)  // mutant takeover
		{ 
    			t=T+1;
			judge=1;
		}			
	}  // end time loop

return judge;

}

/** **************************************************************************************************** **/
//      End of the simulation for one realization
/** **************************************************************************************************** **/


/** **************************************************************************************************** **/
//      Main loop over realizations
/** **************************************************************************************************** **/

int main(){

    FILE* fp1;
    FILE* fp2;

    fp1=fopen("da.txt","w");
    fp2=fopen("da2.txt","w");
    	
	NK=((double)N)/((double)K); // population in each region
	betam=d*beta; // infection rate for mutants
	v=Vmax*4/365; // vaccination rate per infection cycle
	h=H*4/365; // permitted infection rate per infection cycle  
 	
	mu=pow(10,-9); // initial mutation rate 10^(-10.2)
factor=pow(10,0.1); // step for mu in computation, 0.1 orders of magnitude

	srand(time(NULL)); // seed for random number 
    

    
for(wane=0;wane<1;wane=wane+0.01)   // loop for the mutation rate, from 10^(-10.2) to 10^(6.8) step 10^(0.1)
{ 
   	count2=0;  // initiate number of realizations that mutant takes over
	for(count1=0;count1<Realizations;count1++)    // run the simulation for 5000 realizations to compute probability of mutant takeover 
	{
		judge2=model();  // run the realization and check if the mutant took over
		if(judge2>0)
		{
			count2=count2+1;
		}
	}
	
fprintf(fp1,"%.12f  %f\n",wane,count2/(double)Realizations);	
//mu=mu*factor;
}
	
    return 1;
}



