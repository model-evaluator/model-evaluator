package model.url;

public class ErrorUrl extends Url {

	
	public ErrorUrl(String name) {
		super(name);
		this.correspondingOrigin = "StartupOrigin";
	}
}
