
public class MyClass {
    public int a;


    public static void blah(int i){
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

    public static int m() {
	IllegalArgumentException e = new IllegalArgumentException(); 
	try { 
	    throw e; 
	} catch (IllegalStateException e0) { 
	    return 0; 
	} catch (RuntimeException e1) { 
	    return 1; 
	} finally { 
	    return 2;
	}
    }

}
