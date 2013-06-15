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

package de.hentschel.visualdbc.interactive.proving.ui.util.event;

import java.util.EventObject;

import de.hentschel.visualdbc.datasource.model.IDSConnection;
import de.hentschel.visualdbc.dbcmodel.DbcModel;
import de.hentschel.visualdbc.interactive.proving.ui.util.InteractiveConnectionUtil;

/**
 * An event thrown from {@link InteractiveConnectionUtil} and observed via an {@link IInteractiveConnectionUtilListener}.
 * @author Martin Hentschel
 */
public class InteractiveConnectionUtilEvent extends EventObject {
   /**
    * Generated UID.
    */
   private static final long serialVersionUID = 8398545774583006802L;

   /**
    * The {@link IDSConnection}.
    */
   private IDSConnection connection;
   
   /**
    * The {@link DbcModel}.
    */
   private DbcModel model;

   /**
    * Constructor.
    * @param connection The {@link IDSConnection}.
    * @param model The {@link DbcModel}.
    */
   public InteractiveConnectionUtilEvent(IDSConnection connection, DbcModel model) {
      super(InteractiveConnectionUtil.class);
      this.connection = connection;
      this.model = model;
   }

   /**
    * Returns the {@link IDSConnection}.
    * @return The {@link IDSConnection}.
    */
   public IDSConnection getConnection() {
      return connection;
   }

   /**
    * Returns the {@link DbcModel}.
    * @return The {@link DbcModel}.
    */
   public DbcModel getModel() {
      return model;
   }

   /**
    * {@inheritDoc}
    */
   @Override
   public Class<InteractiveConnectionUtil> getSource() {
      return InteractiveConnectionUtil.class;
   }
}