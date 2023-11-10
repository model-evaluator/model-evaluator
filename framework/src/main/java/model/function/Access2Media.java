package model.function;

import org.javers.core.metamodel.annotation.DiffInclude;

import model.Media;

public class Access2Media extends Event {
	
	@DiffInclude
	public String media;
	

	public Access2Media() {
		
	}

}
