package model.url;

public class AboutUrl extends Url {
	
	public AboutUrl(String name) {
		super(name);
		this.scheme = Scheme.About;
		this.corresponding = "about:blank";
		this.correspondingOrigin = "OpaqueOrigin";
	}

}
