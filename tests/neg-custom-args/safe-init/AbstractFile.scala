abstract class AbstractFile {
	def name: String
	val extension: String = name.substring(4)  // error
}

class RemoteFile(url: String) extends AbstractFile {
	val localFile: String = url.hashCode + ".tmp"
	def name: String = {
		val x = 5
		localFile
	}
}
