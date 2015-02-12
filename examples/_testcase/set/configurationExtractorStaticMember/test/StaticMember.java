public class StaticMember {
     private int h;
       public int l;
       static Refer r =new Refer();
       public static int s;
       /*! l | h ; 
        s | h ; 
        !*/
       /*@ ensures true;  
       @*/
       public void compute(int k){
          if(h*2 > k){
             l=r.nl.m + r.x;
             s=h;
          }else{
             l=s;
             s = h+1;
          }
          //change static value
          r.nl.m=1;     
       }
}