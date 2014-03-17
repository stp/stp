#!/bin/bash

for i in {1..5000}
do
  ./muldiv > file
  result=`stp -d -m file`
  if [ $result != "sat" ]; then
      echo "failed"  
      exit
      fi
  echo $result
done
