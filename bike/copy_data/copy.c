#include <stdio.h>
#include <stdlib.h>
#include <time.h>

int
main()
{
  int   ch;
  FILE *sfp;
  FILE *dfp;
  for(int i = 1; i <= 256; i++)
  {
    char sname[FILENAME_MAX] = {0};
    char dname[FILENAME_MAX] = {0};
    sprintf(sname, "iter_data_all_%d", i);
    sprintf(dname, "iter_data_all");

    if((sfp = fopen(sname, "r")) == NULL)
    {
      printf("\aerror\n");
    }
    else
    {
      if((dfp = fopen(dname, "a")) == NULL)
      {
        printf("\aerror\n");
      }
      else
      {
        while((ch = fgetc(sfp)) != EOF)
        {
          fputc(ch, dfp);
        }
        fclose(dfp);
      }
      fclose(sfp);
    }
  }
  return 0;
}