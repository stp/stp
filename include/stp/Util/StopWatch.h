/*
 * StopWatch.h
 *
 *  Created on: 10/04/2012
 *      Author: thansen
 */

#ifndef STOPWATCH_H_
#define STOPWATCH_H_

#include <ctime>

class Stopwatch
{
public:
        Stopwatch() :
                start(std::clock())
        {
        }
        void stop()
        {
                clock_t total = clock() - start;
                cerr << "ticks: " << total << " " << (float(total) / CLOCKS_PER_SEC) << "s" << endl;
        }
        clock_t stop2()
        {
                clock_t total = clock() - start;
                return total;
        }

private:
        std::clock_t start;
};



struct Stopwatch2
{
        Stopwatch2() :
                elapsed(0), start_t(0)
        {
        }
        void stop()
        {
                elapsed+= (clock() - start_t);
                start_t =0;
        }

        void start()
        {
          assert(start_t ==0);
          start_t =  clock();
        }

        std::clock_t elapsed;
        std::clock_t start_t;
};



#endif /* STOPWATCH_H_ */
