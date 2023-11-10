package model;

import java.util.List;

import org.javers.core.metamodel.annotation.Id;

public class LiveBcInfo {
	
	public List<BrowsingContext> bcs;
	
	@Id
	public String currentHandle;
	
	public String correspondingUrl;
	
	public String errorMessage;
	
	public String newBc;
	
	public boolean cameraInUse;
	
	//public Object newTabReference;

}
