package de.uka.ilkd.key.util.script;

import de.uka.ilkd.key.java.Services;

import java.io.Serializable;
import java.util.Date;

import de.uka.ilkd.key.java.Services;

/**
 * @author weigl
 */
public abstract class Interaction implements Serializable {
  private Date created = new Date();
  private boolean favoured = false;

  public String getProofScriptRepresentation(Services services) {
    throw new UnsupportedOperationException();
  }

  public abstract String getMarkdownText();


  public Date getCreated() {
    return created;
  }

  public void setCreated(Date created) {
    this.created = created;
  }

  public boolean isFavoured() {
    return favoured;
  }

  public void setFavoured(boolean favoured) {
    this.favoured = favoured;
  }
}
