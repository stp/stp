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


#endif /* STOPWATCH_H_ */
