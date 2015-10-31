#include <execinfo.h>
#include <stdio.h>
#include <stdlib.h>

#include <inttypes.h>
#include <string.h>
#include <libunwind.h>
#include <unwind.h>

#include <execinfo.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdio.h>


/* Resolve symbol name and source location given the path to the executable
   and an address */
int addr2line(char const * const program_name, void const * const addr)
{
  char addr2line_cmd[512] = {0};

  /* have addr2line map the address to the relent line in the code */
  #ifdef __APPLE__
    /* apple does things differently... */
    sprintf(addr2line_cmd,"atos -o %.256s %p", program_name, addr);
  #else
    sprintf(addr2line_cmd,"addr2line -f -p -e %.256s %p", program_name, addr);
  #endif
    printf ("%s\n", addr2line_cmd);
  /* This will print a nicely formatted string specifying the
     function and source line of the address */
  return system(addr2line_cmd);
}

#define MAX_STACK_FRAMES 64
static void *stack_traces[MAX_STACK_FRAMES];

void
print_trace()
{
  int i, trace_size = 0;
  char **messages = (char **)NULL;

  trace_size = backtrace(stack_traces, MAX_STACK_FRAMES);
  messages = backtrace_symbols(stack_traces, trace_size);

  /* skip the first couple stack frames (as they are this function and
     our handler) and also skip the last frame as it's (always?) junk. */
  // for (i = 3; i < (trace_size - 1); ++i)
  // we'll use this for now so you can see what's going on
  for (i = 0; i < trace_size; ++i)
  {
      int num;
      char fname[1024];
      sscanf(messages[i], "%d    %s *", &num, fname);
    if (addr2line(fname, stack_traces[i]) != 0)
    {
      printf("  error determining line # for: %s\n", messages[i]);
    }
    //printf("%s\n", messages[i]);

  }
  if (messages) { free(messages); }
}




/* Obtain a backtrace and print it to stdout. */
void
print_trace2 ()
{
  void *array[10];
  size_t size;
  char **strings;
  size_t i;

  size = backtrace (array, 10);
  strings = backtrace_symbols (array, size);

  printf ("Obtained %zd stack frames.\n", size);

  for (i = 0; i < size; i++) {
     printf ("%s\n", strings[i]);
  }

  free (strings);
}

//void
//getFileAndLine (unw_word_t addr, char *file, size_t flen, int *line)
//{
//    static char buf[1024];
//    char *p;
//
//    // prepare command to be executed
//    // our program need to be passed after the -e parameter
//    sprintf (buf, "/usr/bin/atos -o ./a.out %" PRIu64, addr);
//    printf ("%s\n", buf);
//    FILE* f = popen (buf, "r");
//
//    if (f == NULL)
//    {
//        perror (buf);
//        return;
//    }
//
//    // get function name
//    fgets (buf, 256, f);
//
//    // get file and line
//    fgets (buf, 256, f);
//
//    if (buf[0] != '?')
//    {
//        int l;
//        char *p = buf;
//
//        // file name is until ':'
//        while (*p != ':')
//        {
//            p++;
//        }
//
//        *p++ = 0;
//        // after file name follows line number
//        strcpy (file , buf);
//        sscanf (p,"%d", line);
//    }
//    else
//    {
//        strcpy (file,"unkown");
//        *line = 0;
//    }
//
//    pclose(f);
//}
//
//void
//print_trace ()
//{
//    char name[256];
//    unw_cursor_t cursor; unw_context_t uc;
//    unw_word_t ip, sp, offp;
//
//    unw_getcontext(&uc);
//    unw_init_local(&cursor, &uc);
//
//    while (unw_step(&cursor) > 0)
//    {
//        char file[256];
//        int line = 0;
//
//        name[0] = '\0';
//        unw_get_proc_name(&cursor, name, 256, &offp);
//        unw_get_reg(&cursor, UNW_REG_IP, &ip);
//        unw_get_reg(&cursor, UNW_REG_SP, &sp);
//
//        //printf ("%s ip = %lx, sp = %lx\n", name, (long) ip, (long) sp);
//        getFileAndLine((long)ip, file, 256, &line);
//        printf("%s in file %s line %d\n", name, file, line);
//    }
//}


void __yield(int v) {}

void assert(e) {
   if (!e) {
        printf ("ASSERTION FAILED\n");
        print_trace ();
        print_trace2 ();
        exit (1);
   }
}


void __yield_local(int v) {}


