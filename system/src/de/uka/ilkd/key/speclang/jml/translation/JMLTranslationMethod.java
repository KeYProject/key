/*
 * To change this template, choose Tools | Templates
 * and open the template in the editor.
 */

package de.uka.ilkd.key.speclang.jml.translation;

import de.uka.ilkd.key.logic.Term;
import de.uka.ilkd.key.speclang.translation.SLTranslationException;


/**
 *
 * @author christoph
 */
public interface JMLTranslationMethod {
    public Term translate(Object ... params) throws SLTranslationException;
}
