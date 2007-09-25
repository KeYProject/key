class Break {

    public static void tryBreak(int i){
       	l1:{
	    try{
		if (i==0) break l1;
	}
	    catch (Exception e){}
	    finally{ 
		i=i+1;
	    }
	}
	i=i+1;
	return i;
    }

}