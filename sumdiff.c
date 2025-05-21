// Written by Robert Gerbicz
// my Long compilation line is: g++ -m64 -I/home/gerbicz/gmp-6.3.0 -L/home/gerbicz/gmp-6.3.0 -O2 -fomit-frame-pointer -m64 -mtune=corei7 -march=corei7 -mavx2 -o sumdiff sumdiff.c -lgmp -lm

#include <cstdio>
#include <cmath>
#include <ctime>
#include <cassert>
#include "gmp.h"
#include <algorithm>

using namespace std;

double zlog(mpz_t n){// notice that a simple conversion to double is not enough since n>2^1024 is possible and that would be overlow in double type
    
    long int exponent;
    double d=mpz_get_d_2exp(&exponent,n);
    // n=d*2^exponent
    
    return log(d)+(double)exponent*log(2.0);
}    

double flog(mpf_t n){
    
    long int exponent;
    double d=mpf_get_d_2exp(&exponent,n);
    // n=d*2^exponent
    
    return log(d)+(double)exponent*log(2.0);
}    

mpf_t *fact;
mpf_t *invfact;
void inits(int max_m,int L){
// precompute the n! and 1/n! rounded values for 0<=n<=2*(max_m+L).
// it is a little lazy implementation since to get (n+1)! and 1/(n+1)! we are using the previously computed n!,1/n! values,
// so we could get a slightly more precision errors (but still pretty small).
     int n,maxn=2*(max_m+L);
     
     fact=(mpf_t*)malloc((maxn+1)*sizeof(mpf_t));
     invfact=(mpf_t*)malloc((maxn+1)*sizeof(mpf_t));
     for(n=0;n<=maxn;n++){
         mpf_init(fact[n]);
         mpf_init(invfact[n]);
     }
     mpf_set_ui(fact[0],1);
     mpf_set_ui(invfact[0],1);
     for(n=1;n<=maxn;n++){
         mpf_mul_ui(fact[n],fact[n-1],n);
         mpf_div_ui(invfact[n],invfact[n-1],n);
     }
}

void get_exact_W(mpz_ptr val,int m,int L,int B){
// calculation of |W(m,L,B)|
    
    if(m==0 || L==0 || B==0){
        mpz_set_ui(val,1);
        return;
    }
    
    int i,k;
    mpz_t b1,b2,tmp;
    mpz_init(b1);
    mpz_init(b2);
    mpz_init(tmp);
    mpz_set_ui(val,0);
    
    mpz_set_ui(b1,1);
    mpz_bin_uiui(b2,m+L,m);
    
    // computation of |W(m,L,B|=sum(k=0,min(m,L/(B+1)),(-1)^k*binomial(m,k)*binomial(m+L-k*(B+1),m))
    // we store also the b1=binomial(m,k) and b2=binomial(m+L-k*(B+1),m) terms
    // to calculate the next two binomials for k+1 use that binomial(m,k+1)=binomial(m,k)*(m-k)/(k+1)
    //         on the other binomial term use (multiple times) the trivial identity of binomial(n-1,k)=binomial(n,k)*(n-k)/n
    for(k=0;k<=min(m,L/(B+1));k++){
        int s=k*(B+1);

        if(k&1)mpz_submul(val,b1,b2);
        else   mpz_addmul(val,b1,b2);
        
        mpz_mul_ui(b1,b1,m-k);
        mpz_divexact_ui(b1,b1,k+1);
        
        mpz_set_ui(tmp,1);for(i=0;i<B+1;i++)mpz_mul_ui(tmp,tmp,L-s-B+i);
        mpz_mul(b2,b2,tmp);        
        mpz_set_ui(tmp,1);for(i=0;i<B+1;i++)mpz_mul_ui(tmp,tmp,m+L-s-i);

        if(mpz_sgn(tmp)!=0)mpz_divexact(b2,b2,tmp);
        
    }
    mpz_clear(b1);
    mpz_clear(b2);
    mpz_clear(tmp);
}

double best=0.0;
void exact_solve_single_value(int m,int L,int B){
// Calculation of the theta value for given U(m,L,B) set.
    int k;
    mpz_t tmp,tmp2,sU,dU,qU,mult;
    mpz_init(tmp);
    mpz_init(tmp2);
    mpz_init(sU);
    mpz_init(dU);
    mpz_init(qU);
    mpz_init(mult);
    
    // |U+U|=|W(m,2*L,2*B)|
    get_exact_W(sU,m,2*L,2*B);
    
    // d(U)=|U-U|=sum(k=0,min(m,L),binomial(m,k)*W(k,L-k,B-1)*W(m-k,L,B))
    // on the sum store mult=binomial(m,k) and use that binomial(m,k+1)=binomial(m,k)*(m-k)/(k+1)
    mpz_set_ui(dU,0);
    mpz_set_ui(mult,1);
    for(k=0;k<=min(m,L);k++){
         get_exact_W(tmp,k,L-k,B-1);
         mpz_mul(tmp,tmp,mult);
         
         get_exact_W(tmp2,m-k,L,B);
         mpz_addmul(dU,tmp,tmp2);
         
         mpz_mul_ui(mult,mult,m-k);
         mpz_divexact_ui(mult,mult,k+1);
    }
    
    // q(U)=2*max(U)+1=(2*B+1)^m −(2*B+1)^(m−t)+2*(L%B)*(2*B+1)^(m−t−1)+1
    int t=L/B;
    if(L%B>0){
       mpz_ui_pow_ui(tmp,2*B+1,m-t-1);
       mpz_mul_ui(qU,tmp,2*(L%B));
    }
    else{
        mpz_set_ui(qU,0);
    }
    mpz_add_ui(qU,qU,1);
    
    mpz_ui_pow_ui(tmp,2*B+1,m-t);
    mpz_sub(qU,qU,tmp);
    mpz_ui_pow_ui(tmp,2*B+1,m);
    mpz_add(qU,qU,tmp);
                
    double dlogsum=zlog(sU);
    double dlogsub=zlog(dU);
    double dlogq=zlog(qU);
    
    // theta=1+(log(|U-U|)-log(|U+U|))/log(1+2*max(U))=1+(log(s(U))-log(d(U)))/log(q(U))
    double theta=1.0+(dlogsub-dlogsum)/dlogq;
    if(theta>best){
       best=theta;
       printf("theta=%lf for U(%d,%d,%d).\n",theta,m,L,B);
       get_exact_W(tmp,m,L,B);
       gmp_printf("|U|=%Zd;\ns(U)=%Zd;\nd(U)=%Zd;\nq(U)=%Zd;\n\n",
       tmp,sU,dU,qU);
    }

    mpz_clear(tmp);
    mpz_clear(tmp2);
    mpz_clear(sU);
    mpz_clear(dU);
    mpz_clear(qU);
    mpz_clear(mult);

    return;
}

void rounded_search(int min_m,int max_m,int L,int min_B,int max_B){
// Search of the theta value for U(m,L,B) using floating point arithmetic
//   where min_m<=m<=max_m, min_B<=B<=max_B, restrict the search further to m<=2*L    
// printing the theta value only if we improved the current best value.
    inits(max_m,L);
    
    int i,k,m,B;
    mpz_t t;
    mpf_t *P,*Q;
    mpf_t tmp,tmp2,sU,dU,qU;
    mpz_init(t);
    mpf_init(tmp);
    mpf_init(tmp2);
    mpf_init(sU);
    mpf_init(dU);
    mpf_init(qU);
    
    int size=min(max_m,2*L);
    P=(mpf_t*)malloc((L+1)*sizeof(mpf_t));
    Q=(mpf_t*)malloc((size+1)*sizeof(mpf_t));
    for(i=0;i<=L;i++)mpf_init(P[i]);
    for(i=0;i<=size;i++)mpf_init(Q[i]);
    
    for(B=min_B;B<=max_B;B++){
        for(k=0;k<=L;k++){
            get_exact_W(t,k,L-k,B-1);
            mpf_set_z(P[k],t);
        }
        for(k=0;k<=size;k++){
            get_exact_W(t,k,L,B);
            mpf_set_z(Q[k],t);
        }
        
        for(m=max(min_m,(L+B-1)/B);m<=min(max_m,2*L);m++){// L<=m*B should be true, so m>=(L+B-1)/B
                                // notice that restrict the search also to m<=2*L, changing it you can also limit the search for the larger m<=B*L
            
            get_exact_W(t,m,2*L,2*B);
            mpf_set_z(sU,t);
                 
            mpf_set_ui(dU,0);
            for(k=0;k<=min(m,L);k++){
                mpf_mul(tmp,fact[m],invfact[k]);
                mpf_mul(tmp,tmp,invfact[m-k]);
                mpf_mul(tmp,tmp,P[k]);
                mpf_mul(tmp,tmp,Q[m-k]);
                mpf_add(dU,dU,tmp);
            }
                
            if(L%B>0){
                mpf_set_ui(tmp,2*B+1);
                mpf_pow_ui(tmp,tmp,m-L/B-1);
                mpf_mul_ui(qU,tmp,2*(L%B));
            }
            else  mpf_set_ui(qU,0);
            mpf_add_ui(qU,qU,1);
    
            mpf_set_ui(tmp,2*B+1);
            mpf_pow_ui(tmp,tmp,m-L/B);
            mpf_sub(qU,qU,tmp);
            mpf_set_ui(tmp,2*B+1);
            mpf_pow_ui(tmp,tmp,m);
            mpf_add(qU,qU,tmp);

            double dlogsum=flog(sU);
            double dlogsub=flog(dU);
            double dlogq=flog(qU);
                
            double theta=1.0+(dlogsub-dlogsum)/dlogq;
            if(theta>best){
                best=theta;
                printf("theta=%lf for U(%d,%d,%d).\n",theta,m,L,B);
                get_exact_W(t,m,L,B);
                mpf_set_z(tmp,t);
                    
                int prec=10;
                printf("|U|=");mpf_out_str(stdout,10,prec,tmp);printf("\n");
                printf("s(U)=");mpf_out_str(stdout,10,prec,sU);printf("\n");
                printf("d(U)=");mpf_out_str(stdout,10,prec,dU);printf("\n");
                printf("q(U)=");mpf_out_str(stdout,10,prec,qU);printf("\n\n");
            }
        }
    }

    for(i=0;i<=L;i++)mpf_clear(P[i]);free(P);
    for(i=0;i<=size;i++)mpf_clear(Q[i]);free(Q);
    mpz_clear(t);
    mpf_clear(tmp);
    mpf_clear(tmp2);
    mpf_clear(sU);
    mpf_clear(dU);
    mpf_clear(qU);

    return;
}


int main(int argc, char* argv[]){
    
    mpf_set_default_prec(64);
    
    int m,L,B,min_m,max_m,min_B,max_B;
    time_t sec=time(NULL);

    if(argc==4){
        m=atoi(argv[1]);
        L=atoi(argv[2]);
        B=atoi(argv[3]);
        exact_solve_single_value(m,L,B);
    }
    else if(argc==6){
        min_m=atoi(argv[1]);
        max_m=atoi(argv[2]);
            L=atoi(argv[3]);
        min_B=atoi(argv[4]);
        max_B=atoi(argv[5]);
        assert(min_m>0 && L>0 && min_B>0);
        
        rounded_search(min_m,max_m,L,min_B,max_B);
    }
    else {
        printf("Program usage:\nFor 3 input parameters find the exact theta value for m L B.\n");
        printf("For 5 input parameters of min_m max_m L min_B max_B do a (floating point) search for all min_m<=m<=max_m (and m<=2*L) and min_B<=B<=max_B.\n");
        return 0;
    }
    printf("Computed in %ld sec.\n",time(NULL)-sec);
    
    return 0;    
}
