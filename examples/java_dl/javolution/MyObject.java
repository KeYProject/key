public class MyObject{

    private static int counter=0;

    private final int hashCode=counter++;

    public int hashCode(){
	return hashCode;
    }

}
