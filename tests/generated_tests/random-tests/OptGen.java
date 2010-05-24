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
