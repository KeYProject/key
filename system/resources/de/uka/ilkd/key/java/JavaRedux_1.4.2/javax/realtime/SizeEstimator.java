package javax.realtime;

public class SizeEstimator{

    public SizeEstimator(){}
           
    public long getEstimate(){}

    public void	reserve(java.lang.Class c, int number){}

    public void	reserve(SizeEstimator size){}

    public void	reserve(SizeEstimator estimator, int number){}

    public void	reserveArray(int length){}

    public void	reserveArray(int length, java.lang.Class type){}

}
