package org.key_project.sed.core.model;

/**
 * An element with a unique ID which never changes.
 * @author Martin Hentschel
 */
public interface ISEDIDElement {
   /**
    * Returns a unique ID which identifies this element uniquely in
    * the whole debug model. The ID must be a valid XML name.
    * @return The unique ID of this element which is a valid XML name.
    */
   public String getId();
}
