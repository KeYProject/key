/*
 * Created on 27.05.2005
 *
 * This file is part of the RECODER library and protected by the LGPL.
 */
package recoder.abstraction;

import java.util.List;

/**
 * @author gutzmann
 */
public interface AnnotationUse {
    List<? extends ElementValuePair> getElementValuePairs();
}
