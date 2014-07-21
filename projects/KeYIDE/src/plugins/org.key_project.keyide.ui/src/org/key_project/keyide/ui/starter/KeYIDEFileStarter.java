/*******************************************************************************
 * Copyright (c) 2014 Karlsruhe Institute of Technology, Germany
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

package org.key_project.keyide.ui.starter;

import org.eclipse.core.resources.IFile;
import org.eclipse.ui.part.FileEditorInput;
import org.key_project.key4eclipse.common.ui.starter.IFileStarter;
import org.key_project.keyide.ui.editor.KeYEditor;
import org.key_project.util.eclipse.WorkbenchUtil;

/**
 * Starts a proof in the KeYIDE user interface integrated in Eclipse.
 * @author Martin Hentschel
 */
public class KeYIDEFileStarter implements IFileStarter {
   /**
    * The unique ID of this starter.
    */
   public static final String STARTER_ID = "org.key_project.keyide.ui.starter.KeYIDEMethodStarter";
   
   /**
    * {@inheritDoc}
    */
   @Override
   public void open(IFile file) throws Exception {
      WorkbenchUtil.getActivePage().openEditor(new FileEditorInput(file), KeYEditor.EDITOR_ID);
   }
}