TOP = ../../../
include $(TOP)scripts/Makefile.common

SRCS =  rewrite.cpp 
OBJS = $(SRCS:.cpp=.o)
CXXFLAGS += -L../../../lib/ 

.PHONY: clean

rr.a: $(OBJS)
	$(RM) $@
	$(AR) qcs $@ $^

rewrite: $(OBJS)  $(TOP)lib/libstp.a  
	$(CXX)   $(CXXFLAGS) $@.o -o $@ -lstp --static

rewrite.o: rewrite.cpp Functionlist.h  rewrite_rule.h  rewrite_system.h  VariableAssignment.h
	$(CXX)   $(CXXFLAGS) rewrite.cpp -c 

clean:
	rm -f $(OBJS) rewrite time_cbitp test_cbitp

upload: rewrite
	strip ./rewrite
	scp -C ./rewrite rimmer.csse.unimelb.edu.au:/home/pgrad/thansen
	scp -C rules_new.smt2 rimmer.csse.unimelb.edu.au:/home/pgrad/thansen
