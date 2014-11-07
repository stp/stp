/********************************************************************
 * AUTHORS: Trevor Hansen, Dan Liew
 *
 * BEGIN DATE: May, 2010
 *
Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in
all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
THE SOFTWARE.
********************************************************************/

import java.util.*;

class OptGen{
  static Collection<String> out;
  static void fork(String opt, boolean del){
    Collection<String> tmp = new LinkedList<String>();
    for(String s:out){
      tmp.add(s+" -"+opt);
      if(!del)
        tmp.add(s);
    }
    out = tmp;
  }
  public static void main(String args[]){
    int num_opts = Integer.parseInt(args[0]);
    String prog = args[1];
    String exclude = args[2];
    String include = args[3];
    
    out = new LinkedList<String>();
    out.add(prog);
    for(int i=0;i<num_opts;i++){
      String s = i+"";
      if(!exclude.contains(s))
        fork(s,include.contains(s));
    }

    for(String s:out){
      String tmp ="echo \""+s+"\";";
      tmp+=s;
      System.out.println(tmp);
    }
  }
}
