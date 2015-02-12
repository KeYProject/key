public class Refer {
   public int x;
   public int y;
   public NextLevel nl;
   public Refer(){
      x=0;
      y=0;
      nl=new NextLevel();
   }
   public Refer(int x,int y){
    
      this.x=x;
      this.y=y;
   }
  
   public int sum(){
      return x+y+nl.m+nl.n;
   }
  
}