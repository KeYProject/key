/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */

package de.uka.ilkd.key.speclang.jml.translation;

import de.uka.ilkd.key.speclang.translation.SLTranslationException;
import de.uka.ilkd.key.speclang.translation.SLTranslationExceptionManager;


/**
 *
 * @author christoph
 */
public interface JMLTranslationMethod {

    public Object translate(SLTranslationExceptionManager excManager,
                            Object... params)
            throws SLTranslationException;
}
