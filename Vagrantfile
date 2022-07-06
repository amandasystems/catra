# -*- mode: ruby -*-
# vi: set ft=ruby :

# All Vagrant configuration is done below. The "2" in Vagrant.configure
# configures the configuration version (we support older styles for
# backwards compatibility). Please don't change it unless you know what
# you're doing.
Vagrant.configure("2") do |config|
  config.vm.box = "ubuntu/jammy64"

  config.vm.network "forwarded_port", guest: 8888, host: 8888, host_ip: "127.0.0.1"

  # Create a private network, which allows host-only access to the machine
  # using a specific IP.
  # config.vm.network "private_network", ip: "192.168.33.10"

  #
  config.vm.provider "virtualbox" do |vb|
      vb.memory = "4096" # You might want to increase this!
  end


  config.vm.provision "shell", inline: <<-SHELL
     apt-get update
     apt-get install -y python3 python3-venv default-jdk parallel make
     su vagrant --command="python3 -m venv /home/vagrant/venv"
     su vagrant --command="/home/vagrant/venv/bin/pip3 install -r experiments/requirements.txt"
     su vagrant --command="curl -fL https://github.com/coursier/launchers/raw/master/cs-x86_64-pc-linux.gz | gzip -d > cs && chmod +x cs && ./cs setup --yes"
     curl -fL https://es-static.fbk.eu/tools/nuxmv/downloads/nuXmv-2.0.0-linux64.tar.gz | tar xzf -
     cp nuXmv-2.0.0-Linux/bin/nuXmv /usr/local/bin/nuxmv
  SHELL
end
