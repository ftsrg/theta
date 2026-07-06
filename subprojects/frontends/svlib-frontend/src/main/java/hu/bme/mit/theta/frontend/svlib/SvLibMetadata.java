package hu.bme.mit.theta.frontend.svlib;

import hu.bme.mit.theta.xcfa.model.MetaData;
import org.jetbrains.annotations.NotNull;

public class SvLibMetadata extends MetaData {

  private final String sourceName;
  private final String tag;

  public SvLibMetadata(String sourceName) {
    this(sourceName, null);
  }

  public SvLibMetadata(String sourceName, String tag) {
    this.sourceName = sourceName;
    this.tag = tag;
  }

  @Override
  @NotNull
  public MetaData combine(@NotNull MetaData other) {
    return isTag() || !other.isSubstantial() ? this : other;
  }

  @Override
  public boolean isSubstantial() {
    return isTag();
  }

  public String getSourceName() {
    return sourceName;
  }

  public String getTag() {
    return tag;
  }

  public boolean isTag() {
    return tag != null;
  }
}
