package model.function;

import org.javers.core.metamodel.annotation.DiffInclude;

public class LocationReplace extends Event {
	
	@DiffInclude
	public String url;
	
	@DiffInclude
	public String response;
	
	@DiffInclude
	public String xFrameOption;
	
	public LocationReplace () {
		
	}

}
