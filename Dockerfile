FROM debian:latest
SHELL ["/bin/bash", "-c"]
RUN apt-get update && apt-get -y install build-essential git curl sudo python3
RUN useradd -ms /bin/bash verity && \ 
	echo '%sudo ALL=(ALL) NOPASSWD:ALL' >> /etc/sudoers && \
	usermod -aG sudo verity
USER verity
WORKDIR /home/verity
COPY --chown=verity:verity . .
RUN make setup && source ~/.elan/env && make verify
