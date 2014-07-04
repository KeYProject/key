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

package de.hentschel.visualdbc.key.ui.adapter;

import java.lang.ref.WeakReference;
import java.util.LinkedList;
import java.util.List;
import java.util.WeakHashMap;

import org.eclipse.core.runtime.IAdaptable;
import org.eclipse.core.runtime.IAdapterFactory;
import org.eclipse.jface.viewers.ISelectionChangedListener;
import org.eclipse.jface.viewers.SelectionChangedEvent;
import org.eclipse.swt.widgets.Shell;
import org.eclipse.ui.IEditorPart;
import org.key_project.key4eclipse.starter.core.util.AbstractProofProvider;
import org.key_project.key4eclipse.starter.core.util.IProofProvider;
import org.key_project.key4eclipse.starter.core.util.event.ProofProviderEvent;
import org.key_project.util.eclipse.swt.SWTUtil;

import de.hentschel.visualdbc.datasource.key.model.KeyConnection;
import de.hentschel.visualdbc.datasource.key.model.KeyProof;
import de.hentschel.visualdbc.datasource.key.model.event.IKeYConnectionListener;
import de.hentschel.visualdbc.datasource.key.model.event.KeYConnectionEvent;
import de.hentschel.visualdbc.datasource.model.IDSConnection;
import de.hentschel.visualdbc.datasource.model.IDSProof;
import de.hentschel.visualdbc.datasource.model.IDSProvable;
import de.hentschel.visualdbc.datasource.model.event.DSConnectionEvent;
import de.hentschel.visualdbc.datasource.model.event.IDSConnectionListener;
import de.hentschel.visualdbc.dbcmodel.DbcModel;
import de.hentschel.visualdbc.dbcmodel.DbcProof;
import de.hentschel.visualdbc.dbcmodel.diagram.part.DbCDiagramEditor;
import de.hentschel.visualdbc.dbcmodel.presentation.DbcmodelEditor;
import de.hentschel.visualdbc.interactive.proving.ui.finder.IDSFinder;
import de.hentschel.visualdbc.interactive.proving.ui.util.DbcModelUtil;
import de.hentschel.visualdbc.interactive.proving.ui.util.FinderUtil;
import de.hentschel.visualdbc.interactive.proving.ui.util.InteractiveConnectionUtil;
import de.hentschel.visualdbc.interactive.proving.ui.util.event.IInteractiveConnectionUtilListener;
import de.hentschel.visualdbc.interactive.proving.ui.util.event.InteractiveConnectionUtilEvent;
import de.hentschel.visualdbc.key.ui.util.LogUtil;
import de.uka.ilkd.key.gui.KeYMediator;
import de.uka.ilkd.key.proof.Proof;
import de.uka.ilkd.key.symbolic_execution.util.KeYEnvironment;
import de.uka.ilkd.key.ui.UserInterface;

/**
 * This {@link IAdapterFactory} allows to convert {@link DbCDiagramEditor}
 * or {@link DbcmodelEditor} instances into an {@link IProofProvider}
 * via {@link IAdaptable#getAdapter(Class)}.
 * @author Martin Hentschel
 */
public class ProofProviderAdapterFactory implements IAdapterFactory {
   /**
    * {@link IEditorPart} mapping to make sure that for each {@link IEditorPart} only one instance of {@link EditorProofProvider} is created. 
    */
   private WeakHashMap<IEditorPart, WeakReference<EditorProofProvider>> editorMapping = new WeakHashMap<IEditorPart, WeakReference<EditorProofProvider>>();

   /**
    * {@inheritDoc}
    */
   @SuppressWarnings("rawtypes")
   @Override
   public Object getAdapter(Object adaptableObject, Class adapterType) {
      if (adaptableObject instanceof DbCDiagramEditor ||
          adaptableObject instanceof DbcmodelEditor) {
         IEditorPart editor = (IEditorPart)adaptableObject;
         synchronized (editorMapping) {
            WeakReference<EditorProofProvider> reference = editorMapping.get(editor);
            if (reference == null || reference.get() == null) {
               EditorProofProvider result = new EditorProofProvider(editor);
               editorMapping.put(editor, new WeakReference<EditorProofProvider>(result));
               InteractiveConnectionUtil.addInteractiveConnectionUtilListener(result);
               return result;
            }
            else {
               return reference.get();
            }
         }
      }
      else {
         return null;
      }
   }

   /**
    * {@inheritDoc}
    */
   @SuppressWarnings("rawtypes")
   @Override
   public Class[] getAdapterList() {
      return new Class[] {IProofProvider.class};
   }
   
   /**
    * This class is used to convert a {@link DbCDiagramEditor} or a {@link DbcmodelEditor}
    * into an {@link IProofProvider}.
    * @author Martin Hentschel
    */
   private static final class EditorProofProvider extends AbstractProofProvider implements ISelectionChangedListener,
                                                                                           IInteractiveConnectionUtilListener,
                                                                                           IKeYConnectionListener,
                                                                                           IDSConnectionListener {
      /**
       * The {@link IEditorPart} which provides {@link DbcProof}s.
       */
      private IEditorPart editor;
      
      /**
       * Constructor.
       * @param editor The {@link IEditorPart} which provides {@link DbcProof}s.
       */
      public EditorProofProvider(IEditorPart editor) {
         this.editor = editor;
         // A remove is not required because weak references are used.
         editor.getEditorSite().getSelectionProvider().addSelectionChangedListener(this);
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public Proof[] getCurrentProofs() {
         try {
            List<DbcProof> dbcProofs = getSelectedDbcProofs();
            List<Proof> result = new LinkedList<Proof>();
            if (!dbcProofs.isEmpty()) {
               DbcModel dbcModel = DbcModelUtil.getModelRoot(dbcProofs.get(0));
               if (dbcModel != null) {
                  IDSConnection connection = InteractiveConnectionUtil.getConnection(dbcModel);
                  if (connection instanceof KeyConnection) {
                     KeyConnection keyConnection = (KeyConnection)connection;
                     if (!keyConnection.hasKeYConnectionListener(this)) {
                        keyConnection.addKeYConnectionListener(this);
                        keyConnection.addConnectionListener(this);
                     }
                     IDSFinder finder = FinderUtil.getDSFinder(connection);
                     if (finder != null) {
                        for (DbcProof dbcProof : dbcProofs) {
                           IDSProvable dsProvable = finder.findProvable(dbcProof.getTarget());
                           IDSProof dsProof = dsProvable.getInteractiveProof(dbcProof.getObligation());
                           if (dsProof instanceof KeyProof) {
                              Proof proof = ((KeyProof) dsProof).getProof();
                              if (proof != null && !proof.isDisposed()) {
                                 result.add(proof);
                              }
                           }
                        }
                     }
                  }
               }
            }
            return result.toArray(new Proof[result.size()]);
         }
         catch (Exception e) {
            LogUtil.getLogger().logError(e);
            return new Proof[0];
         }
      }
      
      /**
       * Lists the selected {@link DbcProof}s.
       * @return The selected {@link DbcProof}s.
       */
      protected List<DbcProof> getSelectedDbcProofs() {
         Object[] selected = SWTUtil.toArray(editor.getEditorSite().getSelectionProvider().getSelection());
         List<DbcProof> dbcProofs = new LinkedList<DbcProof>();
         for (Object obj : selected) {
            if (obj instanceof DbcProof) {
               dbcProofs.add((DbcProof)obj);
            }
            else if (obj instanceof IAdaptable) {
               DbcProof dbcProof = (DbcProof)((IAdaptable)obj).getAdapter(DbcProof.class);
               if (dbcProof != null) {
                  dbcProofs.add(dbcProof);
               }
            }
         }
         return dbcProofs;
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public Proof getCurrentProof() {
         Proof[] proofs = getCurrentProofs();
         return proofs.length >= 1 ? proofs[0] : null;
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public UserInterface getUI() {
         List<DbcProof> dbcProofs = getSelectedDbcProofs();
         UserInterface result = null;
         if (!dbcProofs.isEmpty()) {
            DbcModel dbcModel = DbcModelUtil.getModelRoot(dbcProofs.get(0));
            if (dbcModel != null) {
               IDSConnection connection = InteractiveConnectionUtil.getConnection(dbcModel);
               if (connection instanceof KeyConnection) {
                  result = ((KeyConnection) connection).getUserInterface();
               }
            }
         }
         return result;
      }
      
      /**
       * {@inheritDoc}
       */
      @Override
      public KeYMediator getMediator() {
         UserInterface ui = getUI();
         return ui != null ? ui.getMediator() : null;
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public KeYEnvironment<?> getEnvironment() {
         return null;
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public void selectionChanged(SelectionChangedEvent event) {
         fireCurrentProofsChanged(new ProofProviderEvent(this, 
                                                         getCurrentProofs(), 
                                                         getCurrentProof(), 
                                                         getUI(), 
                                                         getEnvironment()));
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public void connectionOpened(InteractiveConnectionUtilEvent e) {
         // Observe KeYConnection only if required
         if (e.getConnection() instanceof KeyConnection) {
            KeyConnection connection = (KeyConnection)e.getConnection();
            if (!connection.hasKeYConnectionListener(this)) {
               List<DbcProof> dbcProofs = getSelectedDbcProofs();
               if (!dbcProofs.isEmpty()) {
                  DbcModel dbcModel = DbcModelUtil.getModelRoot(dbcProofs.get(0));
                  if (dbcModel != null && dbcModel.equals(e.getModel())) {
                     connection.addKeYConnectionListener(this);
                     connection.addConnectionListener(this);
                  }
               }
            }
         }
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public void interactiveProofStarted(KeYConnectionEvent e) {
         fireCurrentProofsChangedThreadSave();
      }
      
      /**
       * Fires the event thread save to all listeners.
       */
      protected void fireCurrentProofsChangedThreadSave() {
         final Shell shell = editor.getSite().getShell();
         if (shell != null && !shell.isDisposed()) {
            shell.getDisplay().syncExec(new Runnable() {
               @Override
               public void run() {
                  if (!shell.isDisposed()) {
                     fireCurrentProofsChanged(new ProofProviderEvent(EditorProofProvider.this, 
                                                                     getCurrentProofs(), 
                                                                     getCurrentProof(), 
                                                                     getUI(), 
                                                                     getEnvironment()));
                  }
               }
            });
         }
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public void connected(DSConnectionEvent e) {
      }

      /**
       * {@inheritDoc}
       */
      @Override
      public void disconnected(DSConnectionEvent e) {
         fireCurrentProofsChangedThreadSave();
      }
   };
}