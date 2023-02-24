/*
 * Created on 27.11.2005
 *
 * This file is part of the RECODER library and protected by the LGPL.
 *
 */
package recoder.abstraction;

import java.util.List;

/**
 * @author Tobias Gutzmann
 */
public interface TypeArgument {
    WildcardMode getWildcardMode();

    String getTypeName();

    List<? extends TypeArgument> getTypeArguments();

    enum WildcardMode {
        None, // Type()
        Any, // ?
        Extends, // ? extends Type()
        Super // ? super Type()
    }
}
