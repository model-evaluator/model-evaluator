package model.url;

public class ValidBlobUrl extends Url {
	
	
	public ValidBlobUrl(String name) {
		super(name);
		this.scheme = Scheme.Blob;
		this.correspondingOrigin = "BlankOrigin";
	}

}
