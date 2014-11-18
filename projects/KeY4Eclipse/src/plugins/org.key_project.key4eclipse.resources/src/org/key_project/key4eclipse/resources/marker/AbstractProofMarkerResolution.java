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

package org.key_project.key4eclipse.resources.marker;

import org.eclipse.core.resources.IFile;
import org.eclipse.core.resources.IMarker;
import org.eclipse.core.resources.IProject;
import org.eclipse.core.runtime.CoreException;
import org.eclipse.jdt.core.IJavaProject;
import org.eclipse.jdt.core.IMethod;
import org.eclipse.jdt.core.IType;
import org.eclipse.jdt.core.JavaModelException;
import org.eclipse.ui.IMarkerResolution2;
import org.key_project.key4eclipse.resources.util.KeYResourcesUtil;
import org.key_project.key4eclipse.resources.util.LogUtil;
import org.key_project.util.java.StringUtil;
import org.key_project.util.jdt.JDTUtil;

/**
 * Provides the QuickFixes for the KeY{@link IMarker}.
 * @author Stefan Käsdorf
 */
public abstract class AbstractProofMarkerResolution implements IMarkerResolution2 {
   /**
    * The label to show.
    */
   private final String label;
   
   /**
    * The description to show.
    */
   private final String description;
   
   /**
    * Initializes the global variables depending on the given {@link IMarker#getType()}.
    * @param marker - the given {@link IMarker}
    * @throws CoreException 
    */
   public AbstractProofMarkerResolution(IMarker marker) throws CoreException {
      IFile proofFile = KeYResourcesUtil.getProofFile(marker);
      String proofFileName = proofFile != null ? proofFile.getName() : "";
      if (MarkerUtil.CLOSEDMARKER_ID.equals(marker.getType())) {
         description = getClosedMarkerDescriptionPrefix() + proofFileName;
      }
      else if (MarkerUtil.NOTCLOSEDMARKER_ID.equals(marker.getType())) {
         description = getNotClosedMarkerDescriptionPrefix() + proofFileName;
      }
      else {
         description = null;
      }
      this.label = getLabelPrefix() + proofFileName;
   }
   
   /**
    * Returns the closed marker description prefix.
    * @return The closed marker description prefix.
    */
   protected abstract String getClosedMarkerDescriptionPrefix();

   /**
    * Returns the not closed marker description prefix.
    * @return The not closed marker description prefix.
    */
   protected abstract String getNotClosedMarkerDescriptionPrefix();

   /**
    * Returns the label prefix.
    * @return The label prefix.
    */
   protected abstract String getLabelPrefix();

   /**
    * {@inheritDoc}
    */
   @Override
   public String getLabel() {
      return label;
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public void run(IMarker marker) {
      try {
         IFile file = KeYResourcesUtil.getProofFile(marker);
         if (file != null) {
            run(marker, file);
         }
      }
      catch (Exception e) {
         LogUtil.getLogger().logError(e);
         LogUtil.getLogger().openErrorDialog(null, e);
      }
   }
   
   /**
    * Performs the marker resolution.
    * @param marker The {@link IMarker}.
    * @param proofFile The {@link IFile} which contains the proof.
    * @throws Exception Occurred Exception.
    */
   protected abstract void run(IMarker marker, IFile proofFile) throws Exception;

   /**
    * Returns the {@link IMethod} specified by the {@link IMarker} if available.
    * @param marker The {@link IMarker}.
    * @param proofFile The {@link IFile} which contains the proof.
    * @return The specified {@link IMethod} or {@code null} if not available.
    * @throws JavaModelException Occurred Exception.
    */
   protected IMethod findMethod(IMarker marker, IFile proofFile) throws JavaModelException {
      IMethod result = null;
      if (proofFile != null && marker != null) {
         String type = marker.getAttribute(MarkerUtil.TYPE, null);
         String methodName = marker.getAttribute(MarkerUtil.METHOD_NAME, null);
         String methodParameters = marker.getAttribute(MarkerUtil.METHOD_PARAMETERS, null);
         if (!StringUtil.isTrimmedEmpty(type) && !StringUtil.isTrimmedEmpty(methodName)) {
            IProject project = proofFile.getProject();
            if (JDTUtil.isJavaProject(project)) {
               IJavaProject javaProject = JDTUtil.getJavaProject(project);
               IType jdtType = javaProject.findType(type);
               if (jdtType != null) {
                  String[] parameters = !StringUtil.isTrimmedEmpty(methodParameters) ?
                                        methodParameters.split(";") :
                                        new String[0];
                  result = JDTUtil.findJDTMethod(jdtType, methodName, parameters);
               }
            }
         }
      }
      return result;
   }
   
   /**
    * {@inheritDoc}
    */
   @Override
   public String getDescription() {
      return description;
   }
}