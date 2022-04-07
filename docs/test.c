extern void abort(void);
#include <assert.h>
void reach_error() { assert(0); }

#include <pthread.h>
#include <stdlib.h>
#include <stdio.h>
#include <assert.h>

pthread_mutex_t  mutex;
int data = 0;
char *name = NULL;
char *address = "1000NW10thSt";
char letter;
char *zipcode = "66666";
int ind=4;

void *thread1(void *arg)
{
  pthread_mutex_lock(&mutex);
  if (data > 0) 
     free(name);
  pthread_mutex_unlock(&mutex);
  return 0;
}


void *thread2(void *arg)
{
  pthread_mutex_lock(&mutex);
  data++;
  pthread_mutex_unlock(&mutex);
  ind++;
  return 0;
}


void *thread3(void *arg)
{
  pthread_mutex_lock(&mutex);
  letter = name[10];
  pthread_mutex_unlock(&mutex);
  letter = address[12+data];    
  zipcode[ind] = '1';
  return 0;
}


int main()
{
  name = malloc(20);

  pthread_mutex_init(&mutex, 0);

  pthread_t t1, t2, t3;

  pthread_create(&t1, 0, thread1, 0);
  pthread_create(&t2, 0, thread2, 0);
  pthread_create(&t3, 0, thread3, 0);

  pthread_join(t1, 0);
  pthread_join(t2, 0);
  pthread_join(t3, 0);
  
  printf("Letter %d\n", letter);
  return 0;
}

