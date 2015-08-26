/*
 * Util.h
 *
 *  Created on: Mar 13, 2015
 *      Author: laarman
 */

#ifndef LIPTONBIN_LLVM_UTIL_H_
#define LIPTONBIN_LLVM_UTIL_H_

#include <iostream>
#include <string>
#include <llvm/Support/raw_ostream.h>

using namespace std;

#define endll "\n"

#ifndef NDEBUG
#   define LLASSERT(condition, message) \
    do { \
        if (! (condition)) { \
            errs() << "Assertion `" #condition "` failed in " << __FILE__ \
                 << " line " << __LINE__ << ": " << message << "\n"; \
            exit(EXIT_FAILURE); \
        } \
    } while (false)
#else
#   define LLASSERT(condition, message) do { } while (false)
#endif

#endif /* LIPTONBIN_LLVM_UTIL_H_ */
