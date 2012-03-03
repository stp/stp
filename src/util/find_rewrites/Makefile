TOP = ../../../
include $(TOP)scripts/Makefile.common

SRCS =  rewrite.cpp 
OBJS = $(SRCS:.cpp=.o)
CXXFLAGS += -L../../../lib/ 

.PHONY: clean

rewrite: $(OBJS)  $(TOP)lib/libstp.a  
	$(CXX)   $(CXXFLAGS) $@.o -o $@ -lstp 

rewrite.o: rewrite.cpp Functionlist.h  rewrite_rule.h  rewrite_system.h  VariableAssignment.h
	$(CXX)   $(CXXFLAGS) rewrite.cpp -c 

clean:
	rm -f $(OBJS) rewrite time_cbitp test_cbitp
