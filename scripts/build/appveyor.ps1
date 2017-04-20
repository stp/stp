Add-Type -assembly "system.io.compression.filesystem"
$wc = New-Object System.Net.WebClient
$wc.DownloadFile("http://bit.ly/1JPHkL3", "C:\projects\stp\boost_1_59_0.zip")
[io.compression.zipfile]::ExtractToDirectory("C:\projects\stp\boost_1_59_0.zip", "C:\projects\stp\")
