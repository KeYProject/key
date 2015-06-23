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

package org.key_project.sed.key.core.launch;

import java.io.File;
import java.util.LinkedList;
import java.util.List;

import org.eclipse.core.runtime.CoreException;
import org.eclipse.core.runtime.IAdaptable;
import org.eclipse.core.runtime.PlatformObject;
import org.eclipse.debug.core.model.IDebugElement;
import org.eclipse.debug.core.model.IDebugTarget;
import org.eclipse.debug.core.sourcelookup.AbstractSourceLookupParticipant;
import org.key_project.sed.core.model.ISourcePathProvider;
import org.key_project.sed.key.core.model.KeYDebugTarget;
import org.key_project.util.java.CollectionUtil;
import org.key_project.util.java.IFilter;

import de.uka.ilkd.key.proof.JavaModel;
import de.uka.ilkd.key.proof.Proof;

/**
 * {@link AbstractSourceLookupParticipant} implementation for the
 * Symbolic Execution Debugger based on KeY.
 * @author Martin Hentschel
 */
public class KeYSourceLookupParticipant extends AbstractSourceLookupParticipant {
   /**
    * Helper class to compute the source of a custom path.
    * @author Martin Hentschel
    */
   public static class SourceRequest extends PlatformObject implements ISourcePathProvider {
      /**
       * The {@link IDebugTarget} to use.
       */
      private final IDebugTarget debugTarget;
      
      /**
       * The requested source path.
       */
      private final String sourcePath;

      /**
       * Constructor.
       * @param debugTarget The {@link IDebugTarget} to use.
       * @param sourcePath The requested source path.
       */
      public SourceRequest(IDebugTarget debugTarget, String sourcePath) {
         assert debugTarget != null;
         assert sourcePath != null;
         this.debugTarget = debugTarget;
         this.sourcePath = sourcePath;
      }

      /**
       * Returns the {@link IDebugTarget} to use.
       * @return The {@link IDebugTarget} to use.
       */
      public IDebugTarget getDebugTarget() {
         return debugTarget;
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public String getSourcePath() {
         return sourcePath;
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public Object getAdapter(@SuppressWarnings("rawtypes") Class adapter) {
         if (ISourcePathProvider.class.equals(adapter)) {
            return this;
         }
         else {
            return super.getAdapter(adapter);
         }
      }
   }
   
   /**
    * {@inheritDoc}
    */
   public String getSourceName(Object object) throws CoreException {
      if (object instanceof IAdaptable) {
         IAdaptable adaptable = (IAdaptable)object;
         List<File> locations = listAllSourceLocations(adaptable);
         ISourcePathProvider provider = (ISourcePathProvider)adaptable.getAdapter(ISourcePathProvider.class);
         String path = provider.getSourcePath();
         String bestPrefix = findPrefix(locations, path);
         if (bestPrefix != null) {
            return path.substring(bestPrefix.length());
         }
         else {
            return path;
         }
      }
      else {
         return null;
      }
   }

   /**
    * Lists all used source locations defined by the {@link KeYLaunchSettings}.
    * @param adaptable The object which provides the {@link KeYLaunchSettings}.
    * @return All used source locations.
    */
   protected List<File> listAllSourceLocations(IAdaptable adaptable) {
      List<File> result = new LinkedList<File>();
      IDebugTarget target;
      if (adaptable instanceof IDebugElement) {
         target = ((IDebugElement) adaptable).getDebugTarget();
      }
      else if (adaptable instanceof SourceRequest) {
         target = ((SourceRequest) adaptable).getDebugTarget();
      }
      else {
         target = null;
      }
      if (target instanceof KeYDebugTarget) {
         KeYDebugTarget keyTarget = (KeYDebugTarget) target;
         Proof proof = keyTarget.getProof();
         if (proof != null && !proof.isDisposed()) {
            JavaModel javaModel = proof.getServices().getJavaModel();
            if (javaModel.getModelDir() != null) {
               result.add(new File(javaModel.getModelDir()));
            }
            if (javaModel.getClassPathEntries() != null) {
               result.addAll(javaModel.getClassPathEntries());
            }
            if (javaModel.getBootClassPath() != null) {
               result.add(new File(javaModel.getBootClassPath()));
            }
         }
      }
      return result;
   }
   
   /**
    * Selects a prefix of the given path.
    * @param locations The possible prefixes.
    * @param path The path for which the prefix is required.
    * @return The prefix or {@code null} if no prefix is available.
    */
   protected String findPrefix(List<File> locations, final String path) {
      if (path != null) {
         File prefixFile = CollectionUtil.search(locations, new IFilter<File>() {
            @Override
            public boolean select(File element) {
               return path.startsWith(element.toString());
            }
         });
         return prefixFile != null ? prefixFile.toString() : null;
      }
      else {
         return null;
      }
   }
}