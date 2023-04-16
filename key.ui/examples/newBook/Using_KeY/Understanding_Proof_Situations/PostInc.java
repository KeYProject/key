public class PostInc{
  public PostInc rec;
  public int x,y;
  
  /*@ public invariant rec.x >= 0 && rec.y>= 0; @*/
  
  /*@ public normal_behavior
    @ requires true;
    @ ensures rec.x == \old(rec.y) && rec.y == \old(rec.y)+1;
    @*/
  public void postInc(){
    rec.x= rec.y++;
  }
} 
