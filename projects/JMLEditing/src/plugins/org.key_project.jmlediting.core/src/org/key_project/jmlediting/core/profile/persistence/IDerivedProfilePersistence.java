package org.key_project.jmlediting.core.profile.persistence;

import org.key_project.jmlediting.core.profile.IDerivedProfile;
import org.w3c.dom.Document;

public interface IDerivedProfilePersistence {

   Document persist(IDerivedProfile profile) throws ProfilePersistenceException;

   IDerivedProfile read(Document doc) throws ProfilePersistenceException;

}
