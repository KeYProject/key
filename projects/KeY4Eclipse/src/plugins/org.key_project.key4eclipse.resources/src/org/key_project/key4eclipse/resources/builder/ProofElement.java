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

package org.key_project.key4eclipse.resources.builder;

import org.eclipse.core.resources.IFile;
import org.key_project.key4eclipse.starter.core.util.KeYUtil.SourceLocation;

import de.uka.ilkd.key.proof.init.ProofOblInput;

public class ProofElement {
   private ProofOblInput proofObl;
   private IFile javaFile;
   private SourceLocation scl;
   public ProofOblInput getProofObl() {
      return proofObl;
   }
   public IFile getJavaFile() {
      return javaFile;
   }
   public SourceLocation getSourceLocation() {
      return scl;
   }
   
   public ProofElement(ProofOblInput obl, IFile javaFile, SourceLocation scl){
      this.proofObl = obl;
      this.javaFile = javaFile;
      this.scl = scl;
   }
}