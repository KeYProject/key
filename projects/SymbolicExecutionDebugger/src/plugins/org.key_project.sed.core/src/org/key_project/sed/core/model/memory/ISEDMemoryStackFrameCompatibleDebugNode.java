/*******************************************************************************
 * Copyright (c) 2013 Karlsruhe Institute of Technology, Germany 
 *                    Technical University Darmstadt, Germany
 *                    Chalmers University of Technology, Sweden
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Contributors:
 *    Technical University Darmstadt - initial API and implementation and/or initial documentation
 *******************************************************************************/

package org.key_project.sed.core.model.memory;

import org.eclipse.debug.core.model.IStackFrame;
import org.eclipse.debug.core.model.IVariable;
import org.key_project.sed.core.model.impl.AbstractSEDStackFrameCompatibleDebugNode;

/**
 * Provides the set method in a public version of {@link AbstractSEDStackFrameCompatibleDebugNode}.
 * @author Martin Hentschel
 */
public interface ISEDMemoryStackFrameCompatibleDebugNode extends ISEDMemoryDebugNode, IStackFrame {
   /**
    * Sets the line number.
    * @param lineNumber The line number or {@code -1} if it is unknown.
    */
   public void setLineNumber(int lineNumber);
   
   /**
    * Sets the index of the start character.
    * @param charStart The index or {@code -1} if it is unknown.
    */
   public void setCharStart(int charStart);
   
   /**
    * Sets the index of the end character.
    * @param charEnd The index or {@code -1} if it is unknown.
    */
   public void setCharEnd(int charEnd);
   
   /**
    * Sets the source name.
    * @param sourceName The source name to set.
    */
   public void setSourcePath(String sourceName);
   
   /**
    * Adds the given {@link IVariable}.
    * @param variable The {@link IVariable} to add.
    */
   public void addVariable(IVariable variable);
}