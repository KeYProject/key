package de.uka.ilkd.key.util.rifl;

import java.util.List;

import de.uka.ilkd.key.util.KeYExceptionHandler;

/** Simple exception handler which just writes to standard output. 
 * @author bruns 
 */
public class SimpleRIFLExceptionHandler implements KeYExceptionHandler {
    
    static final SimpleRIFLExceptionHandler INSTANCE = 
            new SimpleRIFLExceptionHandler();

    private SimpleRIFLExceptionHandler() {
        // TODO Auto-generated constructor stub
    }

    @Override
    public void reportException(Throwable e) {
        System.out.println(e.toString());
        if (e.getCause() != null) {
            reportException(e.getCause());
        }
    }

    @Override
    public List<Throwable> getExceptions() {
        // TODO Auto-generated method stub
        return null;
    }

    @Override
    public void clear() {
        // TODO Auto-generated method stub

    }

}
