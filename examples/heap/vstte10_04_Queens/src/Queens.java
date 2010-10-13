class Queens {   

    /*@ private normal_behaviour
      @   requires 0 <= pos && pos < board.length;
      @   ensures \result == (\forall int x; 0 <= x && x < pos; 
      @                               board[x] != board[pos] 
      @                               && board[x] - board[pos] != pos - x 
      @                               && board[pos] - board[x] != pos - x);
      @*/
    private static /*@pure@*/ boolean isConsistent(int[] board, int pos) {
	/*@ loop_invariant 0 <= q && q <= pos 
	  @   && (\forall int x; 0 <= x && x < q; 
	  @               board[x] != board[pos] 
          @               && board[x] - board[pos] != pos - x 
          @               && board[pos] - board[x] != pos - x);
	  @ assignable \nothing;
	  @ decreases pos - q;
	  @*/
	for(int q = 0; q < pos; q++) {
	    if (!((board[q] != board[pos])
	           && (board[q] - board[pos] != pos - q)
		   && (board[pos] - board[q] != pos - q))) {
		return false;
	    }
	}
	return true;
    }
    
    
    /*@ private normal_behaviour
      @   requires 0 <= pos && pos < board.length;
      @   requires (\forall int x; 0 <= x && x < board.length; 
      @                            0 <= board[x] && board[x] < board.length);
      @   requires (\forall int p,x; 0 <= x && x < p && p < pos;  
      @                              board[x] != board[p] 
      @                              && board[x] - board[p] != p - x 
      @                              && board[p] - board[x] != p - x);      
      @   assignable board[pos..board.length];
      @   ensures (\forall int x; 0 <= x && x < board.length; 
      @                           0 <= board[x] && board[x] < board.length);
      @   ensures \result ==> (\forall int p,x; 0 <= x && x < p && p < board.length;  
      @                                         board[x] != board[p] 
      @                                         && board[x] - board[p] != p - x 
      @                                         && board[p] - board[x] != p - x);            
      @   measured_by board.length - pos;
      @*/    
    public static /*@nullable@*/ boolean search(int pos, int[] board) {
	/*@ loop_invariant 0 <= i && i <= board.length
	  @   && (\forall int x; 0 <= x && x < board.length; 0 <= board[x] && board[x] < board.length);
	  @ assignable board[pos..board.length];
	  @ decreases board.length - i;
	  @*/
	for(int i = 0; i < board.length; i++) {
	    board[pos] = i;
	    if(isConsistent(board, pos)) {
		if(pos == board.length - 1) {
		    return true;
		} else {
		    boolean complete = search(pos + 1, board);
		    if(complete) {
			return true;
		    }
		}
	    }
	}
	return false;
    }
    
        
    /*public static void main(String[] args) {
	final int[] board = new int[8];
	if(search(0, board)) {
    	    for(int i = 0; i < board.length; i++) {
    		for(int j = 0; j < board.length; j++) {
    		    System.out.print(j == board[i] ? "X" : "O");
    		}
    		System.out.print("\n");
    	    }
	} else {
	    System.out.println("no solution found");
	}
    }*/
}
