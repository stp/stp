TOP = ../../
include $(TOP)scripts/Makefile.common

SRCS =  time_cbitp.cpp test_cbitp.cpp apply.cpp measure.cpp
OBJS = $(SRCS:.cpp=.o)
CXXFLAGS += -L../../lib/ 

.PHONY: clean

measure:  measure.o $(TOP)lib/libstp.a Makefile Functions.o
	$(CXX) $(CXXFLAGS) Functions.o $@.o -o $@ -lstp


apply:  $(OBJS)  $(TOP)lib/libstp.a 
	$(CXX) $(CXXFLAGS) $@.o -o $@ -lstp -static


time_cbitp: $(OBJS)  $(TOP)lib/libstp.a 
	$(CXX) $(CXXFLAGS) $@.o -o $@ -lstp 


test_cbitp: $(OBJS)  $(TOP)lib/libstp.a 
	$(CXX)   $(CXXFLAGS) $@.o -o $@ -lstp 


clean:
	rm -f $(OBJS) rewrite time_cbitp test_cbitp measure
