/*
 * Util.h
 *
 *  Created on: Feb 26, 2015
 *      Author: laarman
 */

#ifndef LIPTONBIN_UTIL_UTIL_H_
#define LIPTONBIN_UTIL_UTIL_H_

#include <iostream>
#include <string>

using namespace std;

#ifndef NDEBUG
#   define ASSERT(condition, message) \
    do { \
        if (! (condition)) { \
            cerr << "Assertion `" #condition "` failed in " << __FILE__ \
                 << " line " << __LINE__ << ": " << message << endl; \
            exit(EXIT_FAILURE); \
        } \
    } while (false)
#else
#   define ASSERT(condition, message) do { } while (false)
#endif

static inline bool
ends_with(string const & value, string const & ending)
{
    if (ending.size() > value.size()) return false;
    return equal(ending.rbegin(), ending.rend(), value.rbegin());
}

template<typename T, typename Y>
static T *select2nd(pair<Y, T> p) { return p.second; }

template<typename T, typename Y>
static T *select1st(pair<T, Y> p) { return p.first; }

#endif /* LIPTONBIN_UTIL_UTIL_H_ */
