public class Client {
    public int x;
    
    /*@ normal_behaviour
      @   requires list.\inv && \disjoint(list.footprint, this.*);
      @   requires list.size() > 0;
      @*/
    void m(List list) {
	x++;
	Object o = list.get(0);
    }
    
    
    /*@ normal_behaviour
      @   requires list.\inv;
      @   ensures \result >= 0;
      @*/
    int n(List list) {
	return list.size();
    }
}
