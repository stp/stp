TOP = ../../
include $(TOP)scripts/Makefile.common

SRCS =  rewrite.cpp
OBJS = $(SRCS:.cpp=.o)
CFLAGS += -L../../lib/ 

.PHONY: clean

rewrite: $(OBJS)  $(TOP)lib/libstp.a 
	rm -f evaluate
	$(CXX)   $(CFLAGS) $^ -o rewrite -lstp 

clean:
	rm -f *.o rewrite
