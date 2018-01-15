// Down-and-out European Continuous Barrier Option Pricing Code with reference to "down_and_out_adjusted_dynamic_prog.cpp"
// The terminal payoff vector that corresponds to indices of the underlying 
// stock prices that are in the black vis-a-vis the barrier have been discounted 
// appropriately using the approach in Baron-Adesi, Fusari and Theal's paper.  
// The terminal payoff vector of those indices that correspond to stock prices
// in the red are zeroed out.
// Written by Shihua Huang

#include <iostream>
#include <iomanip>
#include <cmath>
#include <fstream>
#include <cstdlib>
#include <algorithm>
#include <chrono>
#include <random>
#include "normdist.h"
#include "newmat.h"

using namespace std;

double up_factor, uptick_prob, risk_free_rate, strike_price;
double initial_stock_price, expiration_time, volatility, R, barrier_price;
int no_of_trials, no_of_divisions;
double simulate_call_option_price=0.0;
double simulate_put_option_price=0.0;
double simulate_call_option_price_adjusted = 0.0;
double simulate_put_option_price_adjusted = 0.0;

double max(double a, double b) {
	return (b < a) ? a : b;
}

std::default_random_engine generator;
double get_uniform()
{
	std::uniform_real_distribution <double> distribution(0.0, 1.0);
	double number = distribution(generator);
	return (number);
}

double option_price_put_black_scholes(const double& S,      // spot price
	const double& K,      // Strike (exercise) price,
	const double& r,      // interest rate
	const double& sigma,  // volatility
	const double& time)
{
	double time_sqrt = sqrt(time);
	double d1 = (log(S / K) + r*time) / (sigma*time_sqrt) + 0.5*sigma*time_sqrt;
	double d2 = d1 - (sigma*time_sqrt);
	return K*exp(-r*time)*N(-d2) - S*N(-d1);
};

double option_price_call_black_scholes(const double& S,       // spot (underlying) price
	const double& K,       // strike (exercise) price,
	const double& r,       // interest rate
	const double& sigma,   // volatility 
	const double& time)	  // time to maturity 
{
	double time_sqrt = sqrt(time);
	double d1 = (log(S / K) + r*time) / (sigma*time_sqrt) + 0.5*sigma*time_sqrt;
	double d2 = d1 - (sigma*time_sqrt);
	return S*N(d1) - K*exp(-r*time)*N(d2);
};

double N(const double& z) {
	if (z > 6.0) { return 1.0; }; // this guards against overflow 
	if (z < -6.0) { return 0.0; };
	double b1 = 0.31938153;
	double b2 = -0.356563782;
	double b3 = 1.781477937;
	double b4 = -1.821255978;
	double b5 = 1.330274429;
	double p = 0.2316419;
	double c2 = 0.3989423;
	double a = fabs(z);
	double t = 1.0 / (1.0 + a*p);
	double b = c2*exp((-z)*(z / 2.0));
	double n = ((((b5*t + b4)*t + b3)*t + b2)*t + b1)*t;
	n = 1.0 - b*n;
	if (z < 0.0) n = 1.0 - n;
	return n;
};

float closed_form_down_and_out_european_call_option()
{
	// I took this formula from Wilmott, Howison and Dewynne, "The Mathematics of Financial Derivatives"
	float K = (2 * risk_free_rate) / (volatility*volatility);
	float A = option_price_call_black_scholes(initial_stock_price, strike_price,
		risk_free_rate, volatility, expiration_time);
	float B = (barrier_price*barrier_price) / initial_stock_price;
	float C = pow(initial_stock_price / barrier_price, -(K - 1));
	float D = option_price_call_black_scholes(B, strike_price, risk_free_rate, volatility, expiration_time);
	return (A - D*C);
}

float closed_form_down_and_in_european_put_option()
{
	// just making it easier by renaming the global variables locally
	float S = initial_stock_price;
	float r = risk_free_rate;
	float T = expiration_time;
	float sigma = volatility;
	float H = barrier_price;
	float X = strike_price;

	// Took these formulae from some online reference
	float lambda = (r + ((sigma*sigma) / 2)) / (sigma*sigma);
	float temp = 2 * lambda - 2.0;
	float x1 = (log(S / H) / (sigma*sqrt(T))) + (lambda*sigma*sqrt(T));
	float y = (log(H*H / (S*X)) / (sigma*sqrt(T))) + (lambda*sigma*sqrt(T));
	float y1 = (log(H / S) / (sigma*sqrt(T))) + (lambda*sigma*sqrt(T));
	return (-S*N(-x1) + X*exp(-r*T)*N(-x1 + sigma*sqrt(T)) +
		S*pow(H / S, 2 * lambda)*(N(y) - N(y1)) -
		X*exp(-r*T)*pow(H / S, temp)*(N(y - sigma*sqrt(T)) - N(y1 - sigma*sqrt(T))));
}

float closed_form_down_and_out_european_put_option()
{
	float vanilla_put = option_price_put_black_scholes(initial_stock_price, strike_price,
		risk_free_rate, volatility, expiration_time);
	float put_down_in = closed_form_down_and_in_european_put_option();
	return (vanilla_put - put_down_in);
}
void adjusted_simulation()
{
	double delta_T = expiration_time / ((double)no_of_divisions);
	double delta_R = (risk_free_rate - 0.5*pow(volatility, 2))*delta_T;
	double delta_SD = volatility*sqrt(delta_T);
	for (int j = 0; j < no_of_trials; j++)
	{
		//create 4 variables for recording whether prices have breached barriers. 
		//They are breach_value1,2,3,4 and breach_value_adjusted1,2,3,4 for explicit 
		//simulation and (1-p)adjustment price respectively
		double current_stock_price1 = initial_stock_price;
		double current_stock_price2 = initial_stock_price;
		double current_stock_price3 = initial_stock_price;
		double current_stock_price4 = initial_stock_price;
		double breach_value1 = 1.0;
		double breach_value2 = 1.0;
		double breach_value3 = 1.0;
		double breach_value4 = 1.0;
		double breach_value_adjusted1 = 1.0;
		double breach_value_adjusted2 = 1.0;
		double breach_value_adjusted3 = 1.0;
		double breach_value_adjusted4 = 1.0;
		for (int i = 0; i < no_of_divisions; i++)
		{
			//use box-muller methods to simulate 4 price paths
			double x = get_uniform();
			double y = get_uniform();
			double a = sqrt(-2.0*log(x)) * cos(6.283185307999998*y);
			double b = sqrt(-2.0*log(x)) * sin(6.283185307999998*y);

			current_stock_price1 = current_stock_price1*exp(delta_R + delta_SD*a);
			current_stock_price2 = current_stock_price2*exp(delta_R - delta_SD*a);
			current_stock_price3 = current_stock_price3*exp(delta_R + delta_SD*b);
			current_stock_price4 = current_stock_price4*exp(delta_R - delta_SD*b);
			//see if stock price are not greter than barrier price, 
			//it is knocked out and record the breach_value as 0
			if (current_stock_price1 <= barrier_price)
				breach_value1 = 0.0;
			if (current_stock_price2 <= barrier_price)
				breach_value2 = 0.0;
			if (current_stock_price3 <= barrier_price)
				breach_value3 = 0.0;
			if (current_stock_price4 <= barrier_price)
				breach_value4 = 0.0;
		}
		//calculate the price in each trial as multiplying the payoff by 0 or 1 and divide 4
		simulate_call_option_price += (breach_value1*max(0.0, current_stock_price1 - strike_price) +
			breach_value2*max(0.0, current_stock_price2 - strike_price) +
			breach_value3*max(0.0, current_stock_price3 - strike_price) +
			breach_value4*max(0.0, current_stock_price4 - strike_price)) / 4.0;
		simulate_put_option_price += (breach_value1*max(0.0, strike_price - current_stock_price1) +
			breach_value2*max(0.0, strike_price - current_stock_price2) +
			breach_value3*max(0.0, strike_price - current_stock_price3) +
			breach_value4*max(0.0, strike_price - current_stock_price4)) / 4.0;
		//after simulating the 4-prices-path, we test the last price with barrier price,
		//if it breach the barrier price, the variable breach_value_adjusted should be recorded as 0
		if (current_stock_price1 <= barrier_price)
			breach_value_adjusted1 = 0.0;
		if (current_stock_price2 <= barrier_price)
			breach_value_adjusted2 = 0.0;
		if (current_stock_price3 <= barrier_price)
			breach_value_adjusted3 = 0.0;
		if (current_stock_price4 <= barrier_price)
			breach_value_adjusted4 = 0.0;
		//calculate the probability of breaching barrier price according to equation(1) in assignment instruction
		double probability_stock_path_has_hit_barrier_by_the_time_it_got_here1 =
			exp((-2.0 / (volatility*volatility*expiration_time)) * log(initial_stock_price / barrier_price)*
				log(current_stock_price1 / barrier_price));
		double probability_stock_path_has_hit_barrier_by_the_time_it_got_here2 =
			exp((-2.0 / (volatility*volatility*expiration_time)) * log(initial_stock_price / barrier_price)*
				log(current_stock_price2 / barrier_price));
		double probability_stock_path_has_hit_barrier_by_the_time_it_got_here3 =
			exp((-2.0 / (volatility*volatility*expiration_time)) * log(initial_stock_price / barrier_price)*
				log(current_stock_price3 / barrier_price));
		double probability_stock_path_has_hit_barrier_by_the_time_it_got_here4 =
			exp((-2.0 / (volatility*volatility*expiration_time)) * log(initial_stock_price / barrier_price)*
				log(current_stock_price4 / barrier_price));
		//calculate adjusted price by multipling 1-p
		simulate_call_option_price_adjusted +=
			(breach_value_adjusted1*(1 - probability_stock_path_has_hit_barrier_by_the_time_it_got_here1)*max(0.0, current_stock_price1 - strike_price) +
				breach_value_adjusted2*(1 - probability_stock_path_has_hit_barrier_by_the_time_it_got_here2)*max(0.0, current_stock_price2 - strike_price) +
				breach_value_adjusted3*(1 - probability_stock_path_has_hit_barrier_by_the_time_it_got_here3)*max(0.0, current_stock_price3 - strike_price) +
				breach_value_adjusted4*(1 - probability_stock_path_has_hit_barrier_by_the_time_it_got_here4)*max(0.0, current_stock_price4 - strike_price)) / 4.0;
		simulate_put_option_price_adjusted +=
			(breach_value_adjusted1*(1 - probability_stock_path_has_hit_barrier_by_the_time_it_got_here1)*max(0.0, strike_price - current_stock_price1) +
				breach_value_adjusted2*(1 - probability_stock_path_has_hit_barrier_by_the_time_it_got_here2)*max(0.0, strike_price - current_stock_price2) +
				breach_value_adjusted3*(1 - probability_stock_path_has_hit_barrier_by_the_time_it_got_here3)*max(0.0, strike_price - current_stock_price3) +
				breach_value_adjusted4*(1 - probability_stock_path_has_hit_barrier_by_the_time_it_got_here4)*max(0.0, strike_price - current_stock_price4)) / 4.0;
	}
	//discount two prices to present
	simulate_call_option_price = exp(-risk_free_rate*expiration_time)*(simulate_call_option_price / ((double)no_of_trials));
	simulate_put_option_price = exp(-risk_free_rate*expiration_time)*(simulate_put_option_price / ((double)no_of_trials));
	simulate_call_option_price_adjusted = exp(-risk_free_rate*expiration_time)*(simulate_call_option_price_adjusted / ((double)no_of_trials));
	simulate_put_option_price_adjusted = exp(-risk_free_rate*expiration_time)*(simulate_put_option_price_adjusted / ((double)no_of_trials));
}

int main(int argc, char* argv[])
{
	std::chrono::time_point<std::chrono::system_clock> start, end;
	std::chrono::duration<double> elapsed_time;
	start = std::chrono::system_clock::now();//start calculating the time

	sscanf_s(argv[1], "%lf", &expiration_time);
	sscanf_s(argv[2], "%lf", &risk_free_rate);
	sscanf_s(argv[3], "%lf", &volatility);
	sscanf_s(argv[4], "%lf", &initial_stock_price);
	sscanf_s(argv[5], "%lf", &strike_price);
	sscanf_s(argv[6], "%d", &no_of_trials);
	sscanf_s(argv[7], "%d", &no_of_divisions);
	sscanf_s(argv[8], "%lf", &barrier_price);

	up_factor = exp(volatility*sqrt(expiration_time / ((double)no_of_divisions)));
	R = exp(risk_free_rate*expiration_time / ((double)no_of_divisions));
	uptick_prob = (R - (1 / up_factor)) / (up_factor - (1 / up_factor));

	cout << "European Down-and-Out Continuous Barrier Options Pricing via Monte Carlo Simulation" << endl;
	cout << "Expiration Time (Years) = " << expiration_time << endl;
	cout << "Risk Free Interest Rate = " << risk_free_rate << endl;
	cout << "Volatility (%age of stock value) = " << volatility * 100 << endl;
	cout << "Initial Stock Price = " << initial_stock_price << endl;
	cout << "Strike Price = " << strike_price << endl;
	cout << "Barrier Price = " << barrier_price << endl;
	cout << "Number of Trials = " << no_of_trials << endl;
	cout << "Number of Divisions = " << no_of_divisions << endl;
	cout << "--------------------------------------" << endl;
	cout << "Up Factor = " << up_factor << endl;
	cout << "Uptick Probability = " << uptick_prob << endl;
	cout << "--------------------------------------" << endl;
	adjusted_simulation();
	cout << "The average Call Price by explicit simulation  = " << simulate_call_option_price << endl;
	cout << "The call price using the (1-p)-adjustment term = " << simulate_call_option_price_adjusted << endl;
	cout << "Theoretical Call Price                         = " << closed_form_down_and_out_european_call_option() << endl;
	cout << "--------------------------------------" << endl;
	cout << "The average Put Price by explicit simulation  = " << simulate_put_option_price << endl;
	cout << "The put price using the (1-p)-adjustment term = " << simulate_put_option_price_adjusted << endl;
	cout << "Theoretical Put Price                         = " << closed_form_down_and_out_european_put_option() << endl;
	cout << "--------------------------------------" << endl;

	end = std::chrono::system_clock::now();//stop calculating the time
	elapsed_time = end - start;//calculate the time used
	cout << "Elapsed time to complete: " << elapsed_time.count() << "s\n" << endl;//output the time
}